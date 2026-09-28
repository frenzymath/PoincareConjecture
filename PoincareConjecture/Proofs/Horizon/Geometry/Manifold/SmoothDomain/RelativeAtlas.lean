import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.RegularChart
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Real

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section

namespace Poincare.Manifold

def subtypeRestrictImage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) :
    OpenPartialHomeomorph (↥(e.source ∩ S)) (↥(e.target ∩ T)) := by
  let F : (↥(e.source ∩ S)) → (↥(e.target ∩ T)) := fun x =>
    ⟨e x, e.map_source x.2.1, (h.apply_mem_iff x.2.1).mpr x.2.2⟩
  let G : (↥(e.target ∩ T)) → (↥(e.source ∩ S)) := fun y =>
    ⟨e.symm y, e.symm.map_source y.2.1, (h.symm_apply_mem_iff y.2.1).mpr y.2.2⟩
  let p : PartialEquiv (↥(e.source ∩ S)) (↥(e.target ∩ T)) :=
    { toFun := F
      invFun := G
      source := Set.univ
      target := Set.univ
      map_source' := by simp
      map_target' := by simp
      left_inv' := by
        intro x hx
        apply Subtype.ext
        exact e.left_inv x.2.1
      right_inv' := by
        intro y hy
        apply Subtype.ext
        exact e.right_inv y.2.1 }
  refine
    { toPartialEquiv := p
      open_source := isOpen_univ
      open_target := isOpen_univ
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.continuousOn.comp continuous_subtype_val.continuousOn (by
      intro x hx
      exact x.2.1)).congr
    intro x hx
    rfl

  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.symm.continuousOn.comp continuous_subtype_val.continuousOn (by
      intro x hx
      exact x.2.1)).congr
    intro x hx
    rfl

@[simp] theorem subtypeRestrictImage_apply_coe
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (x : ↥(e.source ∩ S)) :
    ((subtypeRestrictImage e h x : ↥(e.target ∩ T)) : Y) = e x := by
  rfl

@[simp] theorem subtypeRestrictImage_symm_apply_coe
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (y : ↥(e.target ∩ T)) :
    (((subtypeRestrictImage e h).symm y : ↥(e.source ∩ S)) : X) = e.symm y := by
  rfl

def subtypeRestrictImageOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (a : S) (ha : (a : X) ∈ e.source) :
    OpenPartialHomeomorph S T := by
  classical
  have haT : e a ∈ T := (h.apply_mem_iff ha).mpr a.2
  let F : S → T := fun x => if hx : (x : X) ∈ e.source then
    ⟨e x, (h.apply_mem_iff hx).mpr x.2⟩ else ⟨e a, haT⟩
  let G : T → S := fun y => if hy : (y : Y) ∈ e.target then
    ⟨e.symm y, (h.symm_apply_mem_iff hy).mpr y.2⟩ else a
  let p : PartialEquiv S T :=
    { toFun := F
      invFun := G
      source := Subtype.val ⁻¹' e.source
      target := Subtype.val ⁻¹' e.target
      map_source' := by
        intro x hx
        change (x : X) ∈ e.source at hx
        change (F x : Y) ∈ e.target
        simp [F, hx, e.map_source hx]
      map_target' := by
        intro y hy
        change (y : Y) ∈ e.target at hy
        change (G y : X) ∈ e.source
        simp [G, hy, e.symm.map_source hy]
      left_inv' := by
        intro x hx
        change (x : X) ∈ e.source at hx
        apply Subtype.ext
        simp [F, G, hx, e.map_source hx, e.left_inv hx]
      right_inv' := by
        intro y hy
        change (y : Y) ∈ e.target at hy
        apply Subtype.ext
        simp [F, G, hy, e.symm.map_source hy, e.right_inv hy] }
  refine
    { toPartialEquiv := p
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage continuous_subtype_val
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.continuousOn.comp continuous_subtype_val.continuousOn (by
      intro x hx
      exact hx)).congr
    intro x hx
    change (x : X) ∈ e.source at hx
    simp [p, F, hx]
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.symm.continuousOn.comp continuous_subtype_val.continuousOn (by
      intro y hy
      exact hy)).congr
    intro y hy
    change (y : Y) ∈ e.target at hy
    simp [p, G, hy]

@[simp] theorem subtypeRestrictImageOn_apply_coe
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (a : S) (ha : (a : X) ∈ e.source)
    {x : S} (hx : (x : X) ∈ e.source) :
    ((subtypeRestrictImageOn e h a ha x : T) : Y) = e x := by
  simp [subtypeRestrictImageOn, hx]

@[simp] theorem subtypeRestrictImageOn_source
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (a : S) (ha : (a : X) ∈ e.source) :
    (subtypeRestrictImageOn e h a ha).source = Subtype.val ⁻¹' e.source := by
  rfl

@[simp] theorem subtypeRestrictImageOn_target
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (a : S) (ha : (a : X) ∈ e.source) :
    (subtypeRestrictImageOn e h a ha).target = Subtype.val ⁻¹' e.target := by
  rfl

@[reducible] def chartedSpaceOfRelativeCharts {S H : Type*} [TopologicalSpace S]
    [TopologicalSpace H] (charts : S → OpenPartialHomeomorph S H)
    (hsource : ∀ x : S, x ∈ (charts x).source) : ChartedSpace H S :=
  { atlas := Set.range charts
    chartAt := charts
    mem_chart_source := hsource
    chart_mem_atlas := fun x => ⟨x, rfl⟩ }

@[simp] theorem subtypeRestrictImageOn_symm_apply_coe
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y}
    (h : e.IsImage S T) (a : S) (ha : (a : X) ∈ e.source)
    {y : T} (hy : (y : Y) ∈ e.target) :
    (((subtypeRestrictImageOn e h a ha).symm y : S) : X) = e.symm y := by
  simp [subtypeRestrictImageOn, hy]

theorem contDiffOn_corner_transition_of_eqOn
    {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {k : E → E} {kc : H → H} {s r : Set E}
    (hs : IsOpen s) (hk : ContDiffOn 𝕜 ∞ k s)
    (hsub : r ⊆ s)
    (heq : EqOn (I ∘ kc ∘ I.symm) k r) :
    ContDiffOn 𝕜 ∞ (I ∘ kc ∘ I.symm) r := by
  apply (hk.mono hsub).congr
  intro x hx
  exact heq hx

end Poincare.Manifold
