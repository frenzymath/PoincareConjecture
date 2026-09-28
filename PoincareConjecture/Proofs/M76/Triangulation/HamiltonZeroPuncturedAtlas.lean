import PoincareConjecture.Proofs.M76.Mathlib.PuncturedThreeTorusImmersion
import PoincareConjecture.Proofs.M76.Mathlib.ImmersionPLAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "T" => ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle)
local notation "V" => CubeShell.Ambient
local notation "V3" => (Fin 3 → ℝ)





theorem exists_zero_punctured_torus_PL_domain
    (h : OpenPartialHomeomorph V V3) (hsource : h.source = univ) :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let p := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
    let Y := ({p}ᶜ : Set T)
    ∃ (f : T → V) (e : Y → OpenPartialHomeomorph Y V3),
      IsLocalHomeomorphOn f Y ∧ PLDomain e univ ∧
      (∀ i, EqOn (e i) (fun x : Y => h (f x)) (e i).source) ∧
      ∃ (r : ℝ) (i : Y), 0 < r ∧ r ≤ 1 / 64 ∧
        ∀ y : V, ‖y‖ ≤ r →
          ∃ z : Y, (z : T) = (((y.1.1 : StableTorus.Circle),
              (y.1.2 : StableTorus.Circle)), (y.2 : StableTorus.Circle)) ∧
            z ∈ (e i).source ∧ e i z = h y := by
  classical
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let Q := AddCircle.centeredCubeQuotient (4 * (16 : ℝ))
  let p : T := Q 0
  let Y : Set T := {p}ᶜ
  let q : V → T := fun y =>
    (((y.1.1 : StableTorus.Circle), (y.1.2 : StableTorus.Circle)),
      (y.2 : StableTorus.Circle))
  obtain ⟨f, hf, hfixed, _⟩ := StableTorus.exists_punctured_threeTorus_PL_immersion
  have hY : IsOpen Y := isClosed_singleton.isOpen_compl
  have hcomp : IsLocalHomeomorphOn (h ∘ f) Y :=
    (IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn h).comp hf
      (fun _ _ => hsource.symm ▸ mem_univ _)
  obtain ⟨e, he, heq, _, hcompat⟩ :=
    (hcomp.isLocalHomeomorph_domRestrict hY).exists_piecewiseAffine_coordinate_cover
  have hdomain : PLDomain e univ := {
    cover := fun x => ⟨x, he x⟩
    compatible := hcompat
    closed := isClosed_univ
    halfspace := by intro x hx; simp only [frontier_univ, mem_empty_iff_false] at hx
  }
  have hQ0 : (0 : V) ∈ Q.source := by
    rw [AddCircle.centeredCubeQuotient_source]
    norm_num
  have hpcoords : (p.1.1 ≠ 0 ∧ p.1.2 ≠ 0) ∧ p.2 ≠ 0 := by
    have hp := Q.map_source hQ0
    rw [AddCircle.centeredCubeQuotient_target] at hp
    exact hp
  have hzero : q 0 ∈ Y := by
    change q 0 ∉ {p}
    intro hz
    have heqp : q 0 = p := mem_singleton_iff.mp hz
    exact hpcoords.1.1 (congrArg (fun z : T => z.1.1) heqp.symm)
  let i : Y := ⟨q 0, hzero⟩
  let U : Set T := (Subtype.val : Y → T) '' (e i).source
  have hU : IsOpen U := hY.isOpenMap_subtype_val _ (e i).open_source
  have h0U : q 0 ∈ U := ⟨i, he i, rfl⟩
  have hq : Continuous q :=
    (((AddCircle.continuous_mk' (4 * (16 : ℝ))).comp
      (continuous_fst.comp continuous_fst)).prodMk
      ((AddCircle.continuous_mk' (4 * (16 : ℝ))).comp
        (continuous_snd.comp continuous_fst))).prodMk
          ((AddCircle.continuous_mk' (4 * (16 : ℝ))).comp continuous_snd)
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hq) 0 h0U
  let r : ℝ := min (epsilon / 2) (1 / 64)
  have hr : 0 < r := lt_min (half_pos hepsilon) (by norm_num)
  have hr64 : r ≤ 1 / 64 := min_le_right _ _
  have hrepsilon : r < epsilon := (min_le_left _ _).trans_lt (half_lt_self hepsilon)
  refine ⟨f, e, hf, hdomain, heq, r, i, hr, hr64, ?_⟩
  intro y hy
  have hyU : q y ∈ U := hball (mem_ball_zero_iff.mpr (hy.trans_lt hrepsilon))
  obtain ⟨z, hz, hzq⟩ := hyU
  have hcoords : (|y.1.1| ≤ 1 / 64 ∧ |y.1.2| ≤ 1 / 64) ∧ |y.2| ≤ 1 / 64 := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using hy.trans hr64
  have hfy : f (q y) = y := hfixed y.1.1 y.1.2 y.2
    hcoords.1.1 hcoords.1.2 hcoords.2
  refine ⟨z, hzq, hz, ?_⟩
  rw [heq i hz]
  change h (f (z : T)) = h y
  rw [hzq, hfy]

end PoincareConjecture.M76
