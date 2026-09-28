import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.WindingInvariance
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem HasJointPLAnnularIsotopy.depth_eq_rim_iff {G : Ann ≃ₜ Ann}
    (hG : HasJointPLAnnularIsotopy G) (side : Bool) (x : Ann) :
    depth 8 (G x : P2) = (if side then 1 else -1) ↔
      depth 8 (x : P2) = (if side then 1 else -1) := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (range_annulusRimPoint side).symm.subset hx
    have he : x = annulusRimPoint side z :=
      G.injective (hz.symm.trans (hG.rims side z).symm)
    rw [he, depth_annulusRimPoint]
  · intro hx
    obtain ⟨z, rfl⟩ := (range_annulusRimPoint side).symm.subset hx
    rw [hG.rims, depth_annulusRimPoint]

theorem HasJointPLAnnularIsotopy.depth_mem_Ioo_iff {G : Ann ≃ₜ Ann}
    (hG : HasJointPLAnnularIsotopy G) (x : Ann) :
    depth 8 (G x : P2) ∈ Ioo (-1 : ℝ) 1 ↔ depth 8 (x : P2) ∈ Ioo (-1 : ℝ) 1 := by
  have hb := mem_squareAnnulus_iff_depth.mp x.property
  have hbG := mem_squareAnnulus_iff_depth.mp (G x).property
  have hneg := hG.depth_eq_rim_iff false x
  have hpos := hG.depth_eq_rim_iff true x
  simp only [Bool.false_eq_true, ↓reduceIte] at hneg
  simp only [↓reduceIte] at hpos
  constructor
  · intro hx
    refine ⟨lt_of_le_of_ne hb.1 ?_, lt_of_le_of_ne hb.2 ?_⟩
    · intro he
      exact hx.1.ne ((hneg.mpr he.symm).symm)
    · intro he
      exact hx.2.ne (hpos.mpr he)
  · intro hx
    refine ⟨lt_of_le_of_ne hbG.1 ?_, lt_of_le_of_ne hbG.2 ?_⟩
    · intro he
      exact hx.1.ne ((hneg.mp he.symm).symm)
    · intro he
      exact hx.2.ne (hpos.mp he)

theorem exists_finitePL_proper_arc_after_joint_PL_isotopy
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma)
    (f : ℝ → P2) (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    (hfv : ∀ t : I, f t = (gamma t : P2))
    (hgamma₀ : gamma 0 = annulusRimPoint false 0)
    (hgamma₁ : gamma 1 = annulusRimPoint true 0)
    (hproper : ∀ t : I, (t : ℝ) ∈ Ioo (0 : ℝ) 1 →
      depth 8 (gamma t : P2) ∈ Ioo (-1 : ℝ) 1)
    (G : Ann ≃ₜ Ann) (hG : HasJointPLAnnularIsotopy G) :
    ∃ f' : ℝ → P2, FinitePiecewiseAffineOn f' (Icc 0 1) ∧
      (∀ t : I, f' t = (G (gamma t) : P2)) ∧
      Function.Injective (fun t : I => G (gamma t)) ∧
      G (gamma 0) = annulusRimPoint false 0 ∧
      G (gamma 1) = annulusRimPoint true 0 ∧
      ∀ t : I, (t : ℝ) ∈ Ioo (0 : ℝ) 1 →
        depth 8 (G (gamma t) : P2) ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨g, hg, hgv⟩ := hG.isFinitePL
  have hmaps : MapsTo f (Icc (0 : ℝ) 1) Ann := by
    intro t ht
    rw [hfv ⟨t, ht⟩]
    exact (gamma ⟨t, ht⟩).property
  refine ⟨g ∘ f, hg.comp hf hmaps, ?_, G.injective.comp hinj, ?_, ?_, ?_⟩
  · intro t
    change g (f t) = _
    rw [hfv, ← hgv]
  · rw [hgamma₀, hG.rims]
  · rw [hgamma₁, hG.rims]
  · intro t ht
    exact (hG.depth_mem_Ioo_iff (gamma t)).mpr (hproper t ht)

theorem exists_proper_zero_winding_lift_after_joint_PL_isotopy
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma)
    (f : ℝ → P2) (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    (hfv : ∀ t : I, f t = (gamma t : P2))
    (hgamma₀ : gamma 0 = annulusRimPoint false 0)
    (hgamma₁ : gamma 1 = annulusRimPoint true 0)
    (hproper : ∀ t : I, (t : ℝ) ∈ Ioo (0 : ℝ) 1 →
      depth 8 (gamma t : P2) ∈ Ioo (-1 : ℝ) 1)
    (r₀ : ℝ → P2) (hr₀ : FinitePiecewiseAffineOn r₀ (Icc 0 1))
    (hr₀zero : r₀ 0 = (0, -1)) (hr₀one : r₀ 1 = (0, 1))
    (hheight₀ : ∀ t : I, (r₀ t).2 ∈ Icc (-1 : ℝ) 1)
    (hproject₀ : ∀ t : I, annulusMap 8 (by norm_num)
      (((r₀ t).1 : Circle), (r₀ t).2) = gamma t)
    (G : Ann ≃ₜ Ann) (hG : HasJointPLAnnularIsotopy G) :
    ∃ r : ℝ → P2, FinitePiecewiseAffineOn r (Icc 0 1) ∧
      InjOn r (Icc 0 1) ∧ r 0 = (0, -1) ∧ r 1 = (0, 1) ∧
      (∀ t : I, (r t).2 = depth 8 (G (gamma t) : P2)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1) ∧
      (∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = G (gamma t)) ∧
      ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0 := by
  obtain ⟨r, hr, hi, hr0, hr1, hdepth, hproj, htrans⟩ :=
    exists_zero_winding_annular_lift_after_joint_PL_isotopy gamma hinj f hf hfv
      hgamma₀ hgamma₁ r₀ hr₀ hr₀zero hr₀one hheight₀ hproject₀ G hG
  refine ⟨r, hr, hi, hr0, hr1, hdepth, ?_, ?_, hproj, ?_⟩
  · intro t ht
    rw [hdepth ⟨t, ht⟩]
    exact mem_squareAnnulus_iff_depth.mp (G (gamma ⟨t, ht⟩)).property
  · intro t ht
    rw [hdepth ⟨t, ht.1.le, ht.2.le⟩]
    exact (hG.depth_mem_Ioo_iff _).mpr (hproper ⟨t, ht.1.le, ht.2.le⟩ ht)
  · intro s t hs ht k heq
    obtain ⟨hst, hk⟩ := htrans ⟨s, hs⟩ ⟨t, ht⟩ k heq
    exact ⟨congrArg (fun u : I => (u : ℝ)) hst, hk⟩

end PoincareConjecture.M76.Dehn
