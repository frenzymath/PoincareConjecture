import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Bound
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.BundleCompactness
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.DiskExtension
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.DiskLipschitz
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Fillings
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Gram
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Polar.Density
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Polar.Derivatives
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Polar.Integration
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.SmallDisks
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.UniformBounds
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Angular
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Path
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.PeriodicSpeed
import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Triviality
import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Main
import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.UniformRadius
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.Curvature
import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.Extension
import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.Endpoints
import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.Local
import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.LocalTangentMap
import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.RadialNormalization
import PoincareLib.Topology.Homotopy.LoopSpace.Evaluation

/-! Source-name facade for the preserved Mapher area and width proofs. -/

namespace PoincareMT.Proofs.M58
export PoincareMT.LoopSpace (
  angularPoint
  angularPoint_mem_annulus
  angularVector
  contDiff_angularPoint
  contDiff_diskTimeProfile
  contMDiffAt_radial_extension
  contMDiffAt_loop_extension
  contMDiff_periodicFreeLoop
  continuousAt_tangentMap_of_contMDiffAt
  continuous_contraction_time_input
  continuous_freeLoopSpeed
  continuous_loop_eval
  continuous_constantC1Loop
  continuous_loopCircleTangent
  inner_loopCircleTangent
  continuous_iff_values_tangents
  constantLoopMap
  continuous_loop_tangent_eval
  continuous_pathSpeed
  diskTimeProfile
  diskTimeProfile_eq_one
  diskTimeProfile_mem_Icc
  diskTimeProfile_one
  exists_angularPoint
  exists_contraction_derivative_bounds
  exists_diskTimeProfile_derivative_bound
  exists_disk_lipschitz_constant
  exists_local_contraction
  exists_uniform_riemannian_radius
  hasDerivAt_angularPoint
  integral_loopDisk_polar
  isOpen_loopAnnulus
  loopCircle_mem_annulus
  integral_polar_freeLoopSpeed
  integral_polar_loopPlane
  loopPlaneEquivProd
  loopPlaneEquivProd_symm_polar
  loopEvaluation
  loopOfExtension
  loopTangents
  loopValues
  measurePreserving_loopPlaneEquivProd
  mfderiv_radial_extension
  contMDiffOn_radial_extension
  contDiffAt_radialNormalization
  fderiv_radialNormalization_tangent
  mul_parametrizedAreaDensity_le_polar
  norm_angularPoint
  norm_radialNormalization
  pathELength_eq_ofReal_integral_pathSpeed
  pathSpeed
  periodic_freeLoopSpeed
  periodic_periodicFreeLoop
  radialNormalization
  radialNormalization_of_norm_eq_one
  loop_eq_of_fields
  short_loop_family_trivial
  small_loop_filling
  spanningDiskOfC1
  twoVectorArea
  twoVectorArea_change
  twoVectorArea_le)
end PoincareMT.Proofs.M58

namespace PoincareMT.Proofs.M58
export PoincareMT (repairedShortLoopTriviality)
end PoincareMT.Proofs.M58
