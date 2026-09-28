import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.Twist
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Lift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "I" => unitInterval

theorem annularIntegerTwist_real_coordinates (n : ℤ) (s u : ℝ)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (annularIntegerTwist n
      ⟨annulusMap 8 (by norm_num) ((s : Circle), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ ⟨u, hu⟩⟩ : P2) =
      annulusMap 8 (by norm_num) (((s + 16 * (n : ℝ) * (u + 1) : ℝ) : Circle), u) := by
  let t : I := ⟨(u + 1) / 2, by constructor <;> linarith [hu.1, hu.2]⟩
  have ht : 2 * (t : ℝ) - 1 = u := by dsimp [t]; ring
  have hp : (⟨annulusMap 8 (by norm_num) ((s : Circle), u),
      _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ ⟨u, hu⟩⟩ : Ann) =
      annulusCylinderHomeomorph (t, (s : Circle)) := by
    apply Subtype.ext
    rw [annulusCylinderHomeomorph_apply]
    change annulusMap 8 (by norm_num) ((s : Circle), u) =
      annulusMap 8 (by norm_num) ((s : Circle), 2 * (t : ℝ) - 1)
    rw [ht]
  rw [hp, annularIntegerTwist_cylinder, annulusCylinderHomeomorph_apply]
  change annulusMap 8 (by norm_num) ((s : Circle) + ((32 * (n : ℝ) * (t : ℝ) : ℝ) : Circle),
    2 * (t : ℝ) - 1) = _
  rw [ht, ← AddCircle.coe_add]
  congr 2
  apply congrArg (fun z : ℝ => (z : Circle))
  change s + 32 * (n : ℝ) * ((u + 1) / 2) = s + 16 * (n : ℝ) * (u + 1)
  ring

theorem exists_zero_winding_annular_arc_lift
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma)
    (f : ℝ → P2) (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    (hfv : ∀ t : I, f t = (gamma t : P2))
    (hzero : gamma 0 = annulusRimPoint false 0)
    (hone : gamma 1 = annulusRimPoint true 0) :
    ∃ (n : ℤ) (r : ℝ → P2), FinitePiecewiseAffineOn r (Icc 0 1) ∧
      InjOn r (Icc 0 1) ∧ r 0 = (0, -1) ∧ r 1 = (0, 1) ∧
      (∀ t : I, (r t).2 = depth 8 (gamma t : P2)) ∧
      (∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) =
        (annularIntegerTwist (-n) (gamma t) : P2)) ∧
      ∀ (t s : I) (k : ℤ), r t = r s + (32 * (k : ℝ), 0) → t = s ∧ k = 0 := by
  obtain ⟨n, r, hr, hri, hr0, hr1, hdepth, hproj, htranslate⟩ :=
    exists_finitePL_annular_arc_lift gamma hinj f hf hfv hzero hone
  let A : P2 →ᴬ[ℝ] P2 :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap -
      (16 * (n : ℝ)) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap +
        ContinuousAffineMap.const ℝ P2 1)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hA (z : P2) : A z = (z.1 - 16 * (n : ℝ) * (z.2 + 1), z.2) := rfl
  have hAi : Function.Injective A := by
    intro x y hxy
    have hh := congrArg Prod.snd hxy
    have ha := congrArg Prod.fst hxy
    rw [hA, hA] at hh ha
    apply Prod.ext
    · dsimp only at hh ha
      rw [hh] at ha
      linarith
    · exact hh
  refine ⟨n, A ∘ r, hr.postcomp A, hAi.injOn.comp hri (mapsTo_univ _ _), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, hr0, hA]
    norm_num
  · simp only [Function.comp_apply, hr1, hA]
    apply Prod.ext <;> dsimp <;> ring
  · intro t
    exact hdepth t
  · intro t
    have hu : (r t).2 ∈ Icc (-1 : ℝ) 1 :=
      (hdepth t).symm ▸ mem_squareAnnulus_iff_depth.mp (gamma t).property
    have hg : gamma t =
        ⟨annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ ⟨_, hu⟩⟩ :=
      Subtype.ext (hproj t).symm
    rw [hg, annularIntegerTwist_real_coordinates (-n) _ _ hu]
    simp only [Function.comp_apply, hA, Int.cast_neg]
    congr 2
    apply congrArg (fun z : ℝ => (z : Circle))
    ring
  · intro t s k h
    apply htranslate t s k
    have hh := congrArg Prod.snd h
    have ha := congrArg Prod.fst h
    simp only [Function.comp_apply, hA, Prod.fst_add, Prod.snd_add, add_zero] at hh ha
    apply Prod.ext
    · change (r t).1 = (r s).1 + 32 * (k : ℝ)
      rw [hh] at ha
      linarith
    · simpa only [Prod.snd_add, add_zero] using hh

end PoincareConjecture.M76.Dehn
