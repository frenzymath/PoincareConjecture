import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.ProfilePlanar
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

open Matching

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem profilePlanarDiffeomorph_time_smooth {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real)
    {ζ : Real → Real} (hζ : ContDiff Real ∞ ζ)
    (hζrange : ∀ t, ζ t ∈ Ioo (-1 : Real) 1) :
    ContDiff Real ∞ (fun z : Real × E2 =>
      profilePlanarDiffeomorph hρ H a R (ζ z.1) (hζrange z.1) z.2) ∧
    ContDiff Real ∞ (fun z : Real × E2 =>
      (profilePlanarDiffeomorph hρ H a R (ζ z.1) (hζrange z.1)).symm z.2) := by
  have hζp : ContDiff Real ∞ (fun z : Real × E2 => ζ z.1) := hζ.comp contDiff_fst
  constructor
  · have hd : ContDiffOn Real ∞ (fun z : Real × E2 =>
        horizontal (profileCapShear hρ H a R (tangentPlanarLatitude (ζ z.1) z.2))) univ :=
      (contDiffOn_projected_profileCapShear_latitude hρ H a R).comp
        (f := fun z : Real × E2 => (ζ z.1, z.2))
        (hζp.prodMk contDiff_snd).contDiffOn (fun z _ => ⟨hζrange z.1, mem_univ _⟩)
    convert contDiffOn_univ.mp hd using 1
    funext z
    exact profilePlanarDiffeomorph_apply hρ H a R _ _ _
  · let B : Real × E2 → E2 := fun z =>
      planarGraphFlattening (contDiff_profilePlanarDisplacement hρ H a R (ζ z.1)) z.2
    have hB : ContDiff Real ∞ B := by
      have hy : ContDiff Real ∞ (fun z : Real × E2 => z.2 1) :=
        (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp contDiff_snd
      change ContDiff Real ∞ (fun z : Real × E2 => z.2 -
        profileX ρ (H.symm (a + R ^ 2 - ((z.2 1) ^ 2 + (ζ z.1) ^ 2))) •
          EuclideanSpace.single 0 1)
      exact contDiff_snd.sub (((contDiff_profileX hρ).comp
        (H.symm.contDiff.comp (contDiff_const.sub ((hy.pow 2).add (hζp.pow 2))))).smul
          contDiff_const)
    have hd : ContDiffOn Real ∞ (fun z : Real × E2 => tangentPlanarInverse (ζ z.1, B z)) univ :=
      contDiffOn_tangentPlanarInverse.comp (f := fun z : Real × E2 => (ζ z.1, B z))
        (hζp.prodMk hB).contDiffOn
        (fun z _ => ⟨hζrange z.1, mem_univ _⟩)
    exact contDiffOn_univ.mp hd


def horizontalFamilyLift
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2))
    (hQi : ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2)) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := by
  let T : Diffeomorph 𝓘(Real, E2 × Real) 𝓘(Real, E2 × Real)
      (E2 × Real) (E2 × Real) ∞ := {
    toFun z := (Q z.2 z.1, z.2)
    invFun z := ((Q z.2).symm z.1, z.2)
    left_inv z := by simp
    right_inv z := by simp
    contMDiff_toFun := ((hQ.comp (contDiff_snd.prodMk contDiff_fst)).prodMk contDiff_snd).contMDiff
    contMDiff_invFun := ((hQi.comp (contDiff_snd.prodMk contDiff_fst)).prodMk contDiff_snd).contMDiff }
  let C := graphCoordinates (fun _ => 0) contDiff_const
  exact (C.symm.trans T).trans C

theorem horizontalFamilyLift_apply
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2))
    (hQi : ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2)) (p : E3) :
    horizontalFamilyLift Q hQ hQi p =
      vector (Q (p 2) (horizontal p) 0) (Q (p 2) (horizontal p) 1) (p 2) := by
  change vector (Q (p 2 - 0) (horizontal p) 0) (Q (p 2 - 0) (horizontal p) 1)
    ((p 2 - 0) + 0) = _
  simp

@[simp] theorem horizontalFamilyLift_height
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2))
    (hQi : ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2)) (p : E3) :
    horizontalFamilyLift Q hQ hQi p 2 = p 2 := by
  rw [horizontalFamilyLift_apply]
  rfl

private theorem exists_cylindrical_planar_family {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real) :
    ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
      ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
      (∀ t, 1 / 8 ≤ |t| → ∀ p, Q t p = p) ∧
      ∀ t (ht : |t| ≤ 1 / 16), ∀ p,
        Q t (profilePlanarDiffeomorph hρ H a R t (by
          obtain ⟨hl, hu⟩ := abs_le.mp ht
          constructor <;> linarith) p) =
          profilePlanarDiffeomorph hρ H a R 0 (by constructor <;> norm_num) p := by
  let χ : ContDiffBump (0 : Real) :=
    { rIn := 1 / 4, rOut := 1 / 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let κ : ContDiffBump (0 : Real) :=
    { rIn := 1 / 16, rOut := 1 / 8, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let ζ : Real → Real := fun t => χ t * t
  let β : Real → Real := fun t => (1 - κ t) * ζ t
  have hζ : ContDiff Real ∞ ζ := χ.contDiff.mul contDiff_id
  have hβ : ContDiff Real ∞ β := (contDiff_const.sub κ.contDiff).mul hζ
  have hζrange (t : Real) : ζ t ∈ Ioo (-1 : Real) 1 := by
    apply abs_lt.mp
    by_cases ht : |t| < 1 / 2
    · change |χ t * t| < 1
      rw [abs_mul, abs_of_nonneg χ.nonneg]
      have hm := mul_le_mul_of_nonneg_right (show χ t ≤ 1 from χ.le_one) (abs_nonneg t)
      nlinarith
    · have hz : χ t = 0 := χ.zero_of_le_dist (by
        simpa only [Real.dist_eq, sub_zero] using le_of_not_gt ht)
      norm_num [ζ, hz]
  have hβrange (t : Real) : β t ∈ Ioo (-1 : Real) 1 := by
    apply abs_lt.mp
    have ht := abs_lt.mpr (hζrange t)
    change |(1 - κ t) * ζ t| < 1
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr κ.le_one)]
    have hm := mul_le_mul_of_nonneg_right
      (show 1 - κ t ≤ 1 by linarith [show 0 ≤ κ t from κ.nonneg])
      (abs_nonneg (ζ t))
    linarith
  let A : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => profilePlanarDiffeomorph hρ H a R (ζ t) (hζrange t)
  let B : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => profilePlanarDiffeomorph hρ H a R (β t) (hβrange t)
  obtain ⟨hA, hAi⟩ := profilePlanarDiffeomorph_time_smooth hρ H a R hζ hζrange
  obtain ⟨hB, hBi⟩ := profilePlanarDiffeomorph_time_smooth hρ H a R hβ hβrange
  let Q := fun t => (A t).symm.trans (B t)
  have hQ : ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) :=
    hB.comp (f := fun z : Real × E2 => (z.1, (A z.1).symm z.2)) (contDiff_fst.prodMk hAi)
  have hQi : ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) :=
    hA.comp (f := fun z : Real × E2 => (z.1, (B z.1).symm z.2)) (contDiff_fst.prodMk hBi)
  refine ⟨Q, hQ, hQi, ?_, ?_⟩
  · intro t ht p
    have hκ : κ t = 0 := κ.zero_of_le_dist (by simpa only [Real.dist_eq, sub_zero] using ht)
    have hβα : β t = ζ t := by simp [β, hκ]
    change profilePlanarDiffeomorph hρ H a R (β t) (hβrange t)
      ((profilePlanarDiffeomorph hρ H a R (ζ t) (hζrange t)).symm p) = p
    simp only [hβα, Diffeomorph.apply_symm_apply]
  · intro t ht p
    have hζt : ζ t = t := by
      have hc : χ t = 1 := χ.one_of_mem_closedBall (by
        simpa only [mem_closedBall, Real.dist_eq, sub_zero] using
          ht.trans (by norm_num : (1 : Real) / 16 ≤ 1 / 4))
      simp [ζ, hc]
    have hβt : β t = 0 := by
      have hc : κ t = 1 := κ.one_of_mem_closedBall (by
        simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht)
      simp [β, hc]
    change profilePlanarDiffeomorph hρ H a R (β t) (hβrange t)
      ((profilePlanarDiffeomorph hρ H a R (ζ t) (hζrange t)).symm _) = _
    simp only [hβt, hζt, Diffeomorph.symm_apply_apply]



theorem exists_cylindrical_profile_cap {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p, D p 2 = p 2) ∧
      (∀ p, 1 / 8 ≤ |p 2| → D p = p) ∧
      (∀ t : Real, |t| ≤ 1 / 16 → ∀ q : E2,
        D (profileCapShear hρ H a R (tangentPlanarLatitude t q)) =
          sliceAtHeight t (profilePlanarDiffeomorph hρ H a R 0
            (by constructor <;> norm_num) q)) ∧
      ∀ t : Real, |t| ≤ 1 / 16 →
        ((D '' (profileCapShear hρ H a R '' closedBall (0 : E3) 1)) ∩ {p : E3 | p 2 = t} =
          sliceAtHeight t '' (profilePlanarDiffeomorph hρ H a R 0
            (by constructor <;> norm_num) '' closedBall (0 : E2) 1)) ∧
        ((D '' (profileCapShear hρ H a R '' sphere (0 : E3) 1)) ∩ {p : E3 | p 2 = t} =
          sliceAtHeight t '' (profilePlanarDiffeomorph hρ H a R 0
            (by constructor <;> norm_num) '' sphere (0 : E2) 1)) := by
  obtain ⟨Q, hQ, hQi, hQfix, hQcentral⟩ := exists_cylindrical_planar_family hρ H a R
  let D := horizontalFamilyLift Q hQ hQi
  let G := profileCapShear hρ H a R
  let A₀ := profilePlanarDiffeomorph hρ H a R 0 (by constructor <;> norm_num)
  have hheight (p : E3) : D p 2 = p 2 := horizontalFamilyLift_height Q hQ hQi p
  have hmotion (t : Real) (ht : |t| ≤ 1 / 16) (q : E2) :
      D (G (tangentPlanarLatitude t q)) = sliceAtHeight t (A₀ q) := by
    have htI : t ∈ Ioo (-1 : Real) 1 := by
      obtain ⟨hl, hu⟩ := abs_le.mp ht
      constructor <;> linarith
    have hh : G (tangentPlanarLatitude t q) 2 = t := by
      simp [G, tangentPlanarLatitude]
    have hp : horizontal (G (tangentPlanarLatitude t q)) =
        profilePlanarDiffeomorph hρ H a R t htI q :=
      (profilePlanarDiffeomorph_apply hρ H a R t htI q).symm
    rw [horizontalFamilyLift_apply, hh, hp, hQcentral t ht q]
    rfl
  refine ⟨D, hheight, ?_, hmotion, ?_⟩
  · intro p hp
    change horizontalFamilyLift Q hQ hQi p = p
    rw [horizontalFamilyLift_apply, hQfix (p 2) hp]
    ext i
    fin_cases i <;> rfl
  · intro t ht
    have htI : t ∈ Ioo (-1 : Real) 1 := by
      obtain ⟨hl, hu⟩ := abs_le.mp ht
      constructor <;> linarith
    have hsection (S : Set E2) (T : Set E3)
        (hT : tangentPlanarLatitude t '' S = T ∩ {p : E3 | p 2 = t}) :
        (D '' (G '' T)) ∩ {p : E3 | p 2 = t} = sliceAtHeight t '' (A₀ '' S) := by
      ext p
      constructor
      · rintro ⟨⟨z, ⟨x, hx, rfl⟩, rfl⟩, hxt⟩
        have hh : x 2 = t := by
          change D (G x) 2 = t at hxt
          rw [hheight, profileCapShear_two] at hxt
          exact hxt
        obtain ⟨q, hq, hqe⟩ := hT.symm ▸
          (show x ∈ T ∩ {x : E3 | x 2 = t} from ⟨hx, hh⟩)
        refine ⟨A₀ q, ⟨q, hq, rfl⟩, ?_⟩
        rw [← hqe, hmotion t ht q]
      · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
        refine ⟨⟨G (tangentPlanarLatitude t q), ?_, hmotion t ht q⟩, rfl⟩
        exact ⟨tangentPlanarLatitude t q, (hT ▸ mem_image_of_mem _ hq).1, rfl⟩
    refine ⟨hsection _ _ (tangentPlanarLatitude_image_closedBall htI), ?_⟩
    apply hsection
    rw [← range_sphereLatitude htI]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, rfl⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
