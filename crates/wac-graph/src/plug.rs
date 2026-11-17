use crate::{
    types::{are_semver_compatible, ItemKind, SubtypeChecker},
    CompositionGraph, NodeId, PackageId,
};
use thiserror::Error;

/// Represents an error that can occur when plugging components together.
#[derive(Debug, Error)]
pub enum PlugError {
    /// The socket component had no matching imports for the plugs that were provided
    #[error("the socket component had no matching imports for the plugs that were provided")]
    NoPlugHappened,
    /// An error occurred when building the composition graph
    #[error("an error occurred when building the composition graph")]
    GraphError {
        /// The underlying graph error
        #[source]
        source: anyhow::Error,
    },
    /// A plug names a hole the socket doesn't have.
    #[error("the socket component has no component-typed import (hole) named `{hole}`")]
    NoSuchHole {
        /// The hole's name.
        hole: String,
    },
    /// Two plugs name the same hole.
    #[error("hole `{hole}` is given more than one plug")]
    HoleFilledTwice {
        /// The hole's name.
        hole: String,
    },
    /// A plug fits more than one hole.
    #[error(
        "plug `{plug}` fits more than one hole ({}): name the one to fill, as `<hole>=<plug>`",
        holes.iter().map(|h| format!("`{h}`")).collect::<Vec<_>>().join(", ")
    )]
    AmbiguousHole {
        /// The plug's package name.
        plug: String,
        /// The holes it fits.
        holes: Vec<String>,
    },
}

/// A plug for [`plug_with`].
#[derive(Debug, Clone)]
pub struct Plug {
    /// The plug's package.
    pub package: PackageId,
    /// The socket's component-typed import (a *hole*) to pass the plug's
    /// component to. When `None`, the plug fills the one remaining hole its
    /// type fits, or if none, its exports are plugged into the socket's
    /// imports.
    pub hole: Option<String>,
}

/// Take the exports of the plug components and plug them into the socket component.
///
/// A plug whose component fits one of the socket's component-typed imports
/// (a *hole*) is passed to that import instead.
///
/// Note that the `PackageId`s in `plugs` and `socket` must be registered with the `graph`
/// before calling this function.
pub fn plug(
    graph: &mut CompositionGraph,
    plugs: Vec<PackageId>,
    socket: PackageId,
) -> Result<(), PlugError> {
    let plugs = plugs
        .into_iter()
        .map(|package| Plug {
            package,
            hole: None,
        })
        .collect();
    plug_with(graph, plugs, socket)
}

/// Plugs `plugs` into the socket component: each plug's component into a
/// component-typed import of the socket (a *hole*), or the plug's exports
/// into the socket's imports.
///
/// Plugs that name a hole fill it first. Each other plug then fills the one
/// remaining hole its type fits (it's an error if it fits several), or, if it
/// fits none, its exports are plugged into the socket's imports.
///
/// Note that the `PackageId`s in `plugs` and `socket` must be registered with the `graph`
/// before calling this function.
pub fn plug_with(
    graph: &mut CompositionGraph,
    plugs: Vec<Plug>,
    socket: PackageId,
) -> Result<(), PlugError> {
    let socket_instantiation = graph.instantiate(socket);

    // The socket's holes, by name.
    let mut holes = graph.types()[graph[socket].ty()]
        .imports
        .iter()
        .filter(|(_, kind)| matches!(kind, ItemKind::Component(_)))
        .map(|(name, kind)| (name.clone(), *kind))
        .collect::<indexmap::IndexMap<_, _>>();
    let fill = |graph: &mut CompositionGraph, hole: &str, package: PackageId| {
        let component = graph.component(package);
        graph
            .set_instantiation_argument(socket_instantiation, hole, component)
            .map_err(|err| PlugError::GraphError { source: err.into() })
    };

    // Plugs that name their hole.
    for plug in plugs.iter() {
        let Some(hole) = &plug.hole else { continue };
        if !holes.contains_key(hole) {
            return Err(if is_hole(graph, socket, hole) {
                PlugError::HoleFilledTwice { hole: hole.clone() }
            } else {
                PlugError::NoSuchHole { hole: hole.clone() }
            });
        }
        holes.shift_remove(hole);
        fill(graph, hole, plug.package)?;
    }

    for plug in plugs.iter().filter(|p| p.hole.is_none()) {
        // The remaining holes the plug's component fits.
        let plug_kind = ItemKind::Component(graph[plug.package].ty());
        let mut cache = Default::default();
        let mut checker = SubtypeChecker::new(&mut cache);
        let fits = holes
            .iter()
            .filter(|(_, kind)| {
                checker
                    .is_subtype(plug_kind, graph.types(), **kind, graph.types())
                    .is_ok()
            })
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        match fits.as_slice() {
            [] => plug_exports(graph, plug.package, socket, socket_instantiation)?,
            [hole] => {
                holes.shift_remove(hole);
                fill(graph, hole, plug.package)?;
            }
            _ => {
                return Err(PlugError::AmbiguousHole {
                    plug: graph[plug.package].name().to_string(),
                    holes: fits,
                })
            }
        }
    }

    // Check we've actually done any plugging.
    if graph
        .get_instantiation_arguments(socket_instantiation)
        .next()
        .is_none()
    {
        return Err(PlugError::NoPlugHappened);
    }

    // Export all exports from the socket component.
    for name in graph.types()[graph[socket].ty()]
        .exports
        .keys()
        .cloned()
        .collect::<Vec<_>>()
    {
        let export = graph
            .alias_instance_export(socket_instantiation, &name)
            .map_err(|err| PlugError::GraphError { source: err.into() })?;

        graph
            .export(export, &name)
            .map_err(|err| PlugError::GraphError { source: err.into() })?;
    }

    Ok(())
}

/// Whether the socket has a component-typed import named `name`.
fn is_hole(graph: &CompositionGraph, socket: PackageId, name: &str) -> bool {
    matches!(
        graph.types()[graph[socket].ty()].imports.get(name),
        Some(ItemKind::Component(_))
    )
}

/// Instantiates `plug` and passes its exports to the socket's imports of the
/// same name (or a semver-compatible one), where their types fit.
fn plug_exports(
    graph: &mut CompositionGraph,
    plug: PackageId,
    socket: PackageId,
    socket_instantiation: NodeId,
) -> Result<(), PlugError> {
    // Collect matching (plug_export_name, socket_import_name) pairs.
    // The names may differ when matched via semver compatibility.
    let mut plug_exports: Vec<(String, String)> = Vec::new();
    let mut cache = Default::default();
    let mut checker = SubtypeChecker::new(&mut cache);
    for (name, plug_ty) in &graph.types()[graph[plug].ty()].exports {
        // Try exact name match first, then fall back to semver-compatible match
        let matching_import = graph.types()[graph[socket].ty()]
            .imports
            .get(name)
            .map(|ty| (name.clone(), ty))
            .or_else(|| {
                graph.types()[graph[socket].ty()]
                    .imports
                    .iter()
                    .find(|(import_name, _)| are_semver_compatible(name, import_name))
                    .map(|(import_name, ty)| (import_name.clone(), ty))
            });

        if let Some((socket_name, socket_ty)) = matching_import {
            if checker
                .is_subtype(*plug_ty, graph.types(), *socket_ty, graph.types())
                .is_ok()
            {
                plug_exports.push((name.clone(), socket_name));
            }
        }
    }

    // Instantiate the plug component
    let mut plug_instantiation = None;
    for (plug_name, socket_name) in plug_exports {
        log::debug!("using export `{plug_name}` for plug");
        let plug_instantiation = *plug_instantiation.get_or_insert_with(|| graph.instantiate(plug));
        let export = graph
            .alias_instance_export(plug_instantiation, &plug_name)
            .map_err(|err| PlugError::GraphError { source: err.into() })?;
        graph
            .set_instantiation_argument(socket_instantiation, &socket_name, export)
            .map_err(|err| PlugError::GraphError { source: err.into() })?;
    }
    Ok(())
}
