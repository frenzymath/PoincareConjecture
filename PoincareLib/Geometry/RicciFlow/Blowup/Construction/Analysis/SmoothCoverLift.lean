import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Homotopy.Lifting

/-!
# Smooth lifts through an actual covering

Local smooth inverses upgrade continuous lifts to smooth lifts, retaining
the supplied atlases and projection. A simply connected source then has a
smooth lift through a smooth covering with any prescribed basepoint lift.
This is the sphere-lifting step used in Morgan--Tian Claims 9.45 and 11.7,
pp. 208-209 and 270-271.
-/

set_option autoImplicit false

open Set Manifold
open scoped Topology ContDiff

namespace PoincareMT.M30

variable {k : Type*} [NontriviallyNormedField k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace k F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace k G]
  {H : Type*} [TopologicalSpace H]
  {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H'']
  {I : ModelWithCorners k E H} {J : ModelWithCorners k F H'}
  {K : ModelWithCorners k G H''}
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H'' Y]
  {r : WithTop ℕ∞}

/-- A continuous lift through a local diffeomorphism has the same
regularity as its projection, on the supplied source and cover atlases. -/
theorem contMDiff_of_continuous_lift {p : X → Y} {f : A → X}
    (hp : IsLocalDiffeomorph J K r p) (hf : Continuous f)
    (hpf : ContMDiff I K r (p ∘ f)) : ContMDiff I J r f := by
  intro a
  let h := hp (f a)
  have hs := h.localInverse_contMDiffAt.comp a (hpf a)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.preimage_mem_nhds
    (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)] with b hb
  exact (h.localInverse_left_inv hb).symm

/-- A smooth map from a simply connected, locally path-connected source
has a smooth lift through a smooth covering, with the prescribed basepoint. -/
theorem exists_contMDiff_covering_lift
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : X → Y} (hp : IsCoveringMap p)
    (hps : IsLocalDiffeomorph J K r p) {f : A → Y}
    (hf : ContMDiff I K r f) (a : A) (x : X) (hx : p x = f a) :
    ∃ F : A → X, ContMDiff I J r F ∧ F a = x ∧ p ∘ F = f := by
  obtain ⟨F, ⟨hbase, hcomp⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts ⟨f, hf.continuous⟩ a x hx
  refine ⟨F, contMDiff_of_continuous_lift hps F.continuous ?_, hbase, hcomp⟩
  rw [hcomp]
  exact hf

end PoincareMT.M30
