import PoincareConjecture.Proofs.M76.Mathlib.PLAnnularStripCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProduct
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) (1 / 8)
local notation "S" => sphere (0 : V3) 1
local notation "C" => (S ×ˢ I)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1

noncomputable def unitCubeInwardCollarMap (p : V3 × ℝ) : V3 :=
  fun i => PLAnnularStrip.coordinate 2 (p.1 i + 1) p.2 - 1

private theorem collar_width {t : ℝ} (ht : t ∈ I) : 4 * |t| < 2 := by
  rw [abs_of_nonneg ht.1]
  linarith [ht.2]

private theorem exists_abs_eq_norm (x : V3) : ∃ i, |x i| = ‖x‖ := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image
    (fun j : Fin 3 => |x j|) Finset.univ_nonempty
  refine ⟨i, le_antisymm (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i) ?_⟩
  apply (pi_norm_le_iff_of_nonempty x).mpr
  intro j
  simpa only [Real.norm_eq_abs] using hi j (Finset.mem_univ j)

private theorem collar_scalar_bounds {u t : ℝ} (hu : |u| ≤ 1) (ht : t ∈ I) :
    |PLAnnularStrip.coordinate 2 (u + 1) t - 1| ≤ 1 - t := by
  have hu' : u + 1 ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [(abs_le.mp hu).1, (abs_le.mp hu).2]
  have hmem : PLAnnularStrip.coordinate 2 (u + 1) t ∈ Icc t (2 - t) := by
    rw [← PLAnnularStrip.coordinate_image_Icc (collar_width ht)]
    exact mem_image_of_mem _ hu'
  exact abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

private theorem collar_scalar_boundary {u t : ℝ} (hu : |u| = 1) (ht : t ∈ I) :
    |PLAnnularStrip.coordinate 2 (u + 1) t - 1| = 1 - t := by
  have he := PLAnnularStrip.coordinate_endpoints (collar_width ht)
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hu with hu | hu
  · rw [hu]
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    rw [he.2, abs_of_nonneg (by linarith [ht.2])]
    ring
  · rw [hu]
    rw [neg_add_cancel]
    rw [he.1, abs_of_nonpos (by linarith [ht.2])]
    ring

private theorem collar_norm {p : V3 × ℝ} (hp : p ∈ C) :
    ‖unitCubeInwardCollarMap p‖ = 1 - p.2 := by
  have hnorm : ‖p.1‖ = 1 := mem_sphere_zero_iff_norm.mp hp.1
  have hupper : ‖unitCubeInwardCollarMap p‖ ≤ 1 - p.2 := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    change |PLAnnularStrip.coordinate 2 (p.1 i + 1) p.2 - 1| ≤ 1 - p.2
    apply collar_scalar_bounds _ hp.2
    simpa only [Real.norm_eq_abs, hnorm] using norm_le_pi_norm p.1 i
  obtain ⟨i, hi⟩ := exists_abs_eq_norm p.1
  have hedge := collar_scalar_boundary (hi.trans hnorm) hp.2
  have hle := norm_le_pi_norm (unitCubeInwardCollarMap p) i
  change |PLAnnularStrip.coordinate 2 (p.1 i + 1) p.2 - 1| ≤ _ at hle
  exact le_antisymm hupper (hedge ▸ hle)

private theorem collar_injOn : InjOn unitCubeInwardCollarMap C := by
  intro p hp q hq hpq
  have ht : p.2 = q.2 := by
    have hnorm := congrArg norm hpq
    rw [collar_norm hp, collar_norm hq] at hnorm
    linarith
  apply Prod.ext _ ht
  funext i
  have hpbound : |p.1 i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp hp.1]
      using norm_le_pi_norm p.1 i
  have hqbound : |q.1 i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp hq.1]
      using norm_le_pi_norm q.1 i
  have hpi : p.1 i + 1 ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [(abs_le.mp hpbound).1, (abs_le.mp hpbound).2]
  have hqi : q.1 i + 1 ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [(abs_le.mp hqbound).1, (abs_le.mp hqbound).2]
  have hcoord := congrFun hpq i
  change PLAnnularStrip.coordinate 2 (p.1 i + 1) p.2 - 1 =
    PLAnnularStrip.coordinate 2 (q.1 i + 1) q.2 - 1 at hcoord
  rw [← ht] at hcoord
  have heq := (PLAnnularStrip.strictMonoOn_coordinate (collar_width hp.2)).injOn
    hpi hqi (by linarith)
  linarith

private theorem collar_image : unitCubeInwardCollarMap '' C = T := by
  classical
  apply Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    change ‖unitCubeInwardCollarMap p‖ ∈ Icc (7 / 8 : ℝ) 1
    rw [collar_norm hp]
    constructor <;> linarith [hp.2.1, hp.2.2]
  · intro x hx
    let t := 1 - ‖x‖
    have ht : t ∈ I := ⟨by dsimp [t]; linarith [hx.2],
      by dsimp [t]; linarith [hx.1]⟩
    have hex : ∀ i : Fin 3, ∃ u ∈ Icc (0 : ℝ) 2,
        PLAnnularStrip.coordinate 2 u t = x i + 1 := by
      intro i
      have hbound : |x i| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
      have hxi : x i + 1 ∈ Icc t (2 - t) := by
        constructor <;> dsimp [t] <;>
          linarith [(abs_le.mp hbound).1, (abs_le.mp hbound).2]
      rw [← PLAnnularStrip.coordinate_image_Icc (collar_width ht)] at hxi
      exact hxi
    choose u hu he using hex
    let s : V3 := fun i => u i - 1
    have hsu : ‖s‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      change |u i - 1| ≤ 1
      exact abs_le.mpr ⟨by linarith [(hu i).1], by linarith [(hu i).2]⟩
    have hmap : unitCubeInwardCollarMap (s, t) = x := by
      funext i
      change PLAnnularStrip.coordinate 2 (u i - 1 + 1) t - 1 = x i
      rw [sub_add_cancel, he i]
      ring
    obtain ⟨i, hi⟩ := exists_abs_eq_norm x
    have hsphere : ‖s‖ = 1 := by
      have hxi : x i = -‖x‖ ∨ x i = ‖x‖ :=
        ((abs_eq (norm_nonneg x)).mp hi).symm
      have hend := PLAnnularStrip.coordinate_endpoints (collar_width ht)
      have hstrict := (PLAnnularStrip.strictMonoOn_coordinate (collar_width ht)).injOn
      have hui : u i = 0 ∨ u i = 2 := by
        rcases hxi with hxi | hxi
        · left
          apply hstrict (hu i) (by norm_num)
          change PLAnnularStrip.coordinate 2 (u i) t = PLAnnularStrip.coordinate 2 0 t
          rw [he i, hend.1, hxi]
          dsimp [t]
          ring
        · right
          apply hstrict (hu i) (by norm_num)
          change PLAnnularStrip.coordinate 2 (u i) t = PLAnnularStrip.coordinate 2 2 t
          rw [he i, hend.2, hxi]
          dsimp [t]
          ring
      have hsi : |s i| = 1 := by rcases hui with hui | hui <;> norm_num [s, hui]
      have hle : |s i| ≤ ‖s‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm s i
      exact le_antisymm hsu (hsi ▸ hle)
    exact ⟨(s, t), ⟨mem_sphere_zero_iff_norm.mpr hsphere, ht⟩, hmap⟩

private theorem collar_finitePL_on_complex (K : SimplicialComplex ℝ (V3 × ℝ))
    (hK : K.faces.Finite) : FinitePiecewiseAffineOn unitCubeInwardCollarMap K.space := by
  apply FinitePiecewiseAffineOn.pi_on_complex K hK
  intro i
  let a : (V3 × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ V3 ℝ)
  let s : (V3 × ℝ) →ᴬ[ℝ] ℝ :=
    a.toContinuousAffineMap + ContinuousAffineMap.const ℝ (V3 × ℝ) 1
  let t : (V3 × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ V3 ℝ).toContinuousAffineMap
  let c : (V3 × ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ (V3 × ℝ) 2 - s
  have hs := (K.affineOnFaces_affine s).finitePiecewiseAffineOn hK
  have h₁ := PLAnnularStrip.finitePiecewiseAffineOn_cornerCorrection K hK s t
  have h₂ := PLAnnularStrip.finitePiecewiseAffineOn_cornerCorrection K hK c t
  have hone := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ (V3 × ℝ) (1 : ℝ))).finitePiecewiseAffineOn hK
  convert ((hs.add h₁).sub h₂).sub hone using 1
  rfl

theorem locallyPiecewiseAffineOn_unitCubeInwardCollarMap :
    LocallyPiecewiseAffineOn unitCubeInwardCollarMap univ := by
  intro x _
  obtain ⟨K, hK, hxK, hKU⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed isCompact_singleton
      isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
  obtain ⟨J, hJ, hJs, hmap⟩ := collar_finitePL_on_complex K hK
  exact ⟨J, hJ, hJs.symm ▸ hxK (mem_singleton x), hJs.subset.trans hKU, hmap⟩

theorem exists_unitCube_inward_finitePL_collar :
    ∃ e : C ≃ₜ T, e.IsFinitePL ∧
      (∀ p : C, (e p : V3) = unitCubeInwardCollarMap p) ∧
      (∀ p : C, ‖(e p : V3)‖ = 1 - (p : V3 × ℝ).2) ∧
      ∀ p : C, (p : V3 × ℝ).2 = 0 → (e p : V3) = (p : V3 × ℝ).1 := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3 (closedBall (0 : V3) 1) S)
  let K := B.frontierSubcomplex (closedBall (0 : V3) 1)
  have hK : K.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hKs : K.space = S := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 / 8 by norm_num)
  obtain ⟨L, hL, hLs, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  have hLC : L.space = C := by simpa only [hKs, hJs] using hLs
  have hPL : FinitePiecewiseAffineOn unitCubeInwardCollarMap C := by
    rw [← hLC]
    exact collar_finitePL_on_complex L hL
  obtain ⟨e, he, hval⟩ := hPL.exists_homeomorph_image collar_injOn
  let f := e.trans (Homeomorph.setCongr collar_image)
  have hfval (p : C) : (f p : V3) = unitCubeInwardCollarMap p := hval p
  refine ⟨f, ⟨unitCubeInwardCollarMap, hPL, hfval⟩, hfval,
    fun p => ?_, ?_⟩
  · rw [hfval]
    exact collar_norm p.property
  · intro p ht
    rw [hfval]
    funext i
    change PLAnnularStrip.coordinate 2 ((p : V3 × ℝ).1 i + 1)
      (p : V3 × ℝ).2 - 1 = (p : V3 × ℝ).1 i
    rw [ht]
    have hb : |(p : V3 × ℝ).1 i| ≤ 1 := by
      simpa only [Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp p.property.1]
        using norm_le_pi_norm (p : V3 × ℝ).1 i
    rw [PLAnnularStrip.coordinate_eq_self (by simp; linarith [(abs_le.mp hb).1])
      (by simp; linarith [(abs_le.mp hb).2])]
    ring

end PoincareConjecture.M76
