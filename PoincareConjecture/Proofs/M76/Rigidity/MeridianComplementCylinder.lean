import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ComplementaryCircleInterval
import PoincareConjecture.Proofs.M76.Rigidity.MeridianBand

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem mem_image_hamiltonBoundaryCylinder (J : Set ℝ) (x : X) :
    x ∈ hamiltonMeridianCutAmbientMap '' (Q ×ˢ J) ↔
      x.1 ∈ Q ∧ hamiltonSolidTorusCircleEquiv x.2 ∈
        (fun t : ℝ => (t : AddCircle p)) '' J := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz.1, z.2, hz.2, rfl⟩
  · rintro ⟨hx, t, ht, htx⟩
    refine ⟨(x.1, t), ⟨hx, ht⟩, Prod.ext rfl ?_⟩
    exact hamiltonSolidTorusCircleEquiv.injective htx

theorem injOn_hamiltonComplementCylinder {a : ℝ} (ha : 0 < a) :
    InjOn hamiltonMeridianCutAmbientMap (Q ×ˢ Icc a (p - a)) := by
  intro z hz w hw heq
  have hfst : z.1 = w.1 := congrArg (fun x : X => x.1) heq
  have hsnd := congrArg (fun x : X => hamiltonSolidTorusCircleEquiv x.2) heq
  change (z.2 : AddCircle p) = (w.2 : AddCircle p) at hsnd
  exact Prod.ext hfst (AddCircle.injOn_coe_complementaryInterval ha hz.2 hw.2 hsnd)

theorem image_hamiltonComplementCylinder {a : ℝ}
    (ha : 0 < a) (hap : a < p / 2) :
    hamiltonMeridianCutAmbientMap '' (Q ×ˢ Icc a (p - a)) =
      frontier R \ (hamiltonMeridianCutAmbientMap '' (Q ×ˢ Ioo (-a) a)) := by
  ext x
  have hfront : x ∈ frontier R ↔ x.1 ∈ Q := by
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    simp only [mem_prod, mem_univ, and_true]
  change x ∈ hamiltonMeridianCutAmbientMap '' (Q ×ˢ Icc a (p - a)) ↔
    x ∈ frontier R ∧ x ∉ hamiltonMeridianCutAmbientMap '' (Q ×ˢ Ioo (-a) a)
  rw [mem_image_hamiltonBoundaryCylinder, hfront,
    mem_image_hamiltonBoundaryCylinder, AddCircle.image_coe_complementaryInterval ha hap]
  change (_ ∧ ¬ _) ↔ (_ ∧ ¬ (_ ∧ _))
  tauto

theorem hamiltonComplementCylinder_upper (z : V2) (a : ℝ) :
    hamiltonMeridianCutAmbientMap (z, p - a) =
      hamiltonMeridianCutAmbientMap (z, -a) := by
  have hq : (QuotientAddGroup.mk (fun _ : Fin 1 => p - a) : T) =
      QuotientAddGroup.mk (fun _ : Fin 1 => -a) := by
    apply hamiltonSolidTorusCircleEquiv.injective
    change ((p - a : ℝ) : AddCircle p) = ((-a : ℝ) : AddCircle p)
    exact AddCircle.coe_period_sub a
  exact congrArg (fun q : T => (z, q)) hq

theorem exists_hamiltonComplementCylinder_homeomorph {a : ℝ}
    (ha : 0 < a) (hap : a < p / 2) :
    ∃ h : (Q ×ˢ Icc a (p - a) : Set (V2 × ℝ)) ≃ₜ
        (frontier R \ (hamiltonMeridianCutAmbientMap '' (Q ×ˢ Ioo (-a) a)) : Set X),
      ∀ z, (h z : X) = hamiltonMeridianCutAmbientMap z := by
  let : T2Space T := hamiltonSolidTorusCircleEquiv.isEmbedding.t2Space
  let S : Set (V2 × ℝ) := Q ×ˢ Icc a (p - a)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    (show IsCompact S from (isCompact_sphere (0 : V2) 1).prod isCompact_Icc)
  let H : S ≃ₜ hamiltonMeridianCutAmbientMap '' S :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn hamiltonMeridianCutAmbientMap S
        (injOn_hamiltonComplementCylinder ha))
      ((continuous_hamiltonMeridianCutAmbientMap.comp continuous_subtype_val).subtype_mk _)
  exact ⟨H.trans (Homeomorph.setCongr (image_hamiltonComplementCylinder ha hap)),
    fun _ => rfl⟩

end PoincareConjecture.M76
