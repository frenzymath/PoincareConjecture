import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth charts on their actual open source and target

Partial smooth charts restrict to diffeomorphisms of open submanifolds,
and open inclusions are local diffeomorphisms. These operations keep the
physical buffer carrier in Morgan--Tian, Lemma 16.8, pp. 372-373.
See M44 derivation 37.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareMT.M44

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace G N]

/-- Restrict a partial chart to its literal open source and target.
Source: the physical collar restriction in Lemma 16.8, pp. 372-373;
M44 derivation 37. -/
def sourceTargetDiffeomorph (e : PartialDiffeomorph I J M N ∞) :
    Diffeomorph I J (⟨e.source, e.open_source⟩ : Opens M)
      (⟨e.target, e.open_target⟩ : Opens N) ∞ where
  toFun x := ⟨e x, e.map_source x.2⟩
  invFun y := ⟨e.invFun y, e.map_target y.2⟩
  left_inv x := Subtype.ext (e.left_inv x.2)
  right_inv y := Subtype.ext (e.right_inv y.2)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (⟨e.target, e.open_target⟩ : Opens N) _).mp
    intro x
    exact contMDiffAt_subtype_iff.mpr
      (e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds x.2))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (⟨e.source, e.open_source⟩ : Opens M) _).mp
    intro y
    exact contMDiffAt_subtype_iff.mpr
      (e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds y.2))

/-- Inclusion of an open submanifold is locally a diffeomorphism.
Source: the buffered-carrier argument in Lemma 16.8, pp. 372-373;
M44 derivation 37. -/
theorem open_inclusion_isLocalDiffeomorph (U : Opens M) :
    IsLocalDiffeomorph I I ∞ (Subtype.val : U → M) := by
  intro x
  let hne : Nonempty U := ⟨x⟩
  let e := U.openPartialHomeomorphSubtypeCoe hne
  have hi : ContMDiffOn I I ∞ e.symm e.target := by
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target y).mp
    apply contMDiffWithinAt_id.congr
    · intro z hz
      exact e.right_inv hz
    · exact e.right_inv hy
  let d : PartialDiffeomorph I I U M ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := hi }
  exact d.isLocalDiffeomorphAt I I ∞ (mem_univ x)

/-- The original chart valued in its actual open target, extended by
a fixed target point outside its source. Source: Lemma 16.8,
pp. 372-373; M44 derivation 37. -/
noncomputable def targetChart (e : PartialDiffeomorph I J M N ∞)
    (p : (⟨e.target, e.open_target⟩ : Opens N)) :
    M → (⟨e.target, e.open_target⟩ : Opens N) := by
  classical
  exact fun x => if hx : x ∈ e.source then ⟨e x, e.map_source hx⟩ else p

/-- The target-valued chart agrees with the original map on its
literal source. Source: Lemma 16.8, pp. 372-373; M44 derivation 37. -/
theorem targetChart_val (e : PartialDiffeomorph I J M N ∞)
    (p : (⟨e.target, e.open_target⟩ : Opens N)) {x : M} (hx : x ∈ e.source) :
    (targetChart e p x).1 = e x := by
  simp only [targetChart, dif_pos hx]

/-- The target-valued chart is smooth on the original source, with
the inherited open-submanifold structure. Source: Lemma 16.8,
pp. 372-373; M44 derivation 37. -/
theorem contMDiffOn_targetChart (e : PartialDiffeomorph I J M N ∞)
    (p : (⟨e.target, e.open_target⟩ : Opens N)) :
    ContMDiffOn I J ∞ (targetChart e p) e.source := by
  intro x hx
  apply (ContMDiffWithinAt.subtypeVal_comp_iff
    (⟨e.target, e.open_target⟩ : Opens N) _ _ _).mp
  apply (e.contMDiffOn_toFun x hx).congr
  · intro y hy
    exact targetChart_val e p hy
  · exact targetChart_val e p hx

/-- The target-valued chart is a partial diffeomorphism onto the
whole physical buffer carrier. Source: Lemma 16.8, pp. 372-373;
M44 derivation 37. -/
noncomputable def targetPartialDiffeomorph (e : PartialDiffeomorph I J M N ∞)
    (p : (⟨e.target, e.open_target⟩ : Opens N)) :
    PartialDiffeomorph I J M (⟨e.target, e.open_target⟩ : Opens N) ∞ where
  toFun := targetChart e p
  invFun y := e.invFun y.1
  source := e.source
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun y _ => e.map_target y.2
  left_inv' := fun x hx => by
    rw [targetChart_val e p hx]
    exact e.left_inv hx
  right_inv' := fun y _ => by
    apply Subtype.ext
    exact (targetChart_val e p (e.map_target y.2)).trans (e.right_inv y.2)
  open_source := e.open_source
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiffOn_targetChart e p
  contMDiffOn_invFun :=
    (contMDiff_subtype_val.comp (sourceTargetDiffeomorph e).symm.contMDiff).contMDiffOn

end PoincareMT.M44
