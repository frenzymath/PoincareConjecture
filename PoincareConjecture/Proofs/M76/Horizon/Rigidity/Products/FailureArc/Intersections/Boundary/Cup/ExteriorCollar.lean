import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.UnionDisk

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_boundary_cup_exterior_collar
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {c : P2 → E} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    {B S : Set E} (hcS : MapsTo c source S) (hBS : B ⊆ S)
    (htrim : B ∩ (c '' halfSource true) = c '' arm 1)
    {f : E → X} (hf : ContinuousOn f S) (hfi : InjOn f S)
    {τ : C3 → X} {R T C Sigma : Set X}
    (hperiod : ∀ p ∈ source, f (c p) = τ ((p.2, p.2), p.1))
    (hT : ∀ z ∈ tube, τ z ∈ T ↔ z.1.2 = -z.1.1)
    (hfR : MapsTo f S R)
    (hcap : C ∩ (f '' S) = f '' B)
    (hCS : f '' B ⊆ Sigma) (hSC : Sigma ⊆ C ∪ T) :
    ∃ p : I × I → X, Continuous p ∧ (∀ z, p z ∈ R) ∧
      (∀ t : I, p (t, ⟨0, by norm_num⟩) ∈ f '' B) ∧
      (∀ z, p z ∈ Sigma ↔ (z.2 : ℝ) = 0) ∧
      (∀ z, p z = f (c ((z.1 : ℝ), 1 - (z.2 : ℝ) / 2))) ∧
      range p = f '' (c '' (I ×ˢ Icc (1 / 2 : ℝ) 1)) := by
  let q : I × I → P2 := fun z ↦ ((z.1 : ℝ), 1 - (z.2 : ℝ) / 2)
  have hqc : Continuous q := by fun_prop
  have hq (z : I × I) : q z ∈ halfSource true := by
    refine ⟨z.1.property, ?_⟩
    change 0 ≤ 1 - (z.2 : ℝ) / 2 ∧ 1 - (z.2 : ℝ) / 2 ≤ 1
    constructor <;> linarith [z.2.property.1, z.2.property.2]
  have hqS (z : I × I) : q z ∈ source := halfSource_subset_source true (hq z)
  let p : I × I → X := fun z ↦ f (c (q z))
  have hp : Continuous p := hf.comp_continuous (hc.continuousOn.comp_continuous hqc hqS)
    (fun z ↦ hcS (hqS z))
  have hp0 (t : I) : p (t, ⟨0, by norm_num⟩) ∈ f '' B := by
    have ht : c ((t : ℝ), 1) ∈ B :=
      (htrim.superset ⟨((t : ℝ), 1), ⟨t.property, rfl⟩, rfl⟩).1
    exact ⟨c ((t : ℝ), 1), ht, by simp only [p, q, zero_div, sub_zero]⟩
  have hpT (z : I × I) : p z ∉ T := by
    change f (c (q z)) ∉ T
    rw [hperiod _ (hqS z), hT _ ⟨⟨(hqS z).2, (hqS z).2⟩, (hqS z).1⟩]
    change ¬ (1 - (z.2 : ℝ) / 2 = -(1 - (z.2 : ℝ) / 2))
    intro h
    linarith [z.2.property.2]
  have hproper (z : I × I) : p z ∈ Sigma ↔ (z.2 : ℝ) = 0 := by
    constructor
    · intro hz
      have hzC := (hSC hz).resolve_right (hpT z)
      have hzB := hcap.subset ⟨hzC, ⟨c (q z), hcS (hqS z), rfl⟩⟩
      obtain ⟨x, hx, hxp⟩ := hzB
      have heq : x = c (q z) := hfi (hBS hx) (hcS (hqS z)) hxp
      have hcB : c (q z) ∈ B := heq ▸ hx
      obtain ⟨r, hr, hrc⟩ := htrim.subset ⟨hcB, ⟨q z, hq z, rfl⟩⟩
      have hrS : r ∈ source := ⟨hr.1, by rw [show r.2 = 1 from hr.2]; norm_num⟩
      have heq' := hci hrS (hqS z) hrc
      have hheight : 1 = 1 - (z.2 : ℝ) / 2 :=
        (show r.2 = 1 from hr.2).symm.trans (congrArg Prod.snd heq')
      linarith
    · intro hz
      have hzero : z.2 = (⟨0, by norm_num⟩ : I) := Subtype.ext hz
      have hzEq : z = (z.1, (⟨0, by norm_num⟩ : I)) := Prod.ext rfl hzero
      rw [hzEq]
      exact hCS (hp0 z.1)
  refine ⟨p, hp, fun z ↦ hfR (hcS (hqS z)), hp0, hproper, fun _ ↦ rfl, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    refine ⟨c (q z), ⟨q z, ⟨z.1.property, ?_⟩, rfl⟩, rfl⟩
    change 1 / 2 ≤ 1 - (z.2 : ℝ) / 2 ∧ 1 - (z.2 : ℝ) / 2 ≤ 1
    constructor <;> linarith [z.2.property.1, z.2.property.2]
  · rintro _ ⟨x, ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩, rfl⟩
    have hs : 2 * (1 - u) ∈ I := by constructor <;> linarith [hu.1, hu.2]
    refine ⟨(⟨t, ht⟩, ⟨2 * (1 - u), hs⟩), ?_⟩
    change f (c (t, 1 - 2 * (1 - u) / 2)) = f (c (t, u))
    congr 2
    ring_nf

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup
