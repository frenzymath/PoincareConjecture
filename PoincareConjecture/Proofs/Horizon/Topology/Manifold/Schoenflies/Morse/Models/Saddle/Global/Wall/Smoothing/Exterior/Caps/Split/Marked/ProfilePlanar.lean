import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.ProfileShear
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.PlanarGerm
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.GraphPatch



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

open Matching

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

def profilePlanarDisplacement (ρ : Real → Real) (H : Real ≃ₘ[Real] Real)
    (a R t y : Real) : Real :=
  profileX ρ (H.symm (a + R ^ 2 - (y ^ 2 + t ^ 2)))

theorem contDiff_profilePlanarDisplacement {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R t : Real) :
    ContDiff Real ∞ (profilePlanarDisplacement ρ H a R t) :=
  (contDiff_profileX hρ).comp
    (H.symm.contDiff.comp (contDiff_const.sub ((contDiff_id.pow 2).add contDiff_const)))



def profilePlanarDiffeomorph {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R t : Real) (ht : t ∈ Ioo (-1 : Real) 1) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
  (tangentPlanarDiffeomorph t ht).trans
    (planarGraphFlattening (contDiff_profilePlanarDisplacement hρ H a R t)).symm

theorem profilePlanarDiffeomorph_apply {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R t : Real) (ht : t ∈ Ioo (-1 : Real) 1) (q : E2) :
    profilePlanarDiffeomorph hρ H a R t ht q =
      horizontal (profileCapShear hρ H a R (tangentPlanarLatitude t q)) := by
  change tangentPlanarMap (t, q) +
    profilePlanarDisplacement ρ H a R t (tangentPlanarMap (t, q) 1) •
      EuclideanSpace.single 0 1 = _
  ext i
  fin_cases i
  · change (tangentPlanarMap (t, q) +
      profilePlanarDisplacement ρ H a R t (tangentPlanarMap (t, q) 1) •
        (EuclideanSpace.single 0 1 : E2)) 0 = profileCapShear hρ H a R (tangentPlanarLatitude t q) 0
    simp [profilePlanarDisplacement, profileCapShift, tangentRadiusSq, tangentPlanarLatitude,
      tangentFlatShear_zero]
  · change (tangentPlanarMap (t, q) +
      profilePlanarDisplacement ρ H a R t (tangentPlanarMap (t, q) 1) •
        (EuclideanSpace.single 0 1 : E2)) 1 = profileCapShear hρ H a R (tangentPlanarLatitude t q) 1
    simp [tangentPlanarLatitude]

theorem contDiffOn_projected_profileCapShear_latitude {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real) :
    ContDiffOn Real ∞ (fun z : Real × E2 =>
      horizontal (profileCapShear hρ H a R (tangentPlanarLatitude z.1 z.2)))
        (Ioo (-1 : Real) 1 ×ˢ univ) :=
  horizontal_contDiff.comp_contDiffOn
    ((profileCapShear hρ H a R).contDiff.comp_contDiffOn contDiffOn_tangentPlanarLatitude)

theorem profilePlanarDiffeomorph_closedBall {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R t : Real) (ht : t ∈ Ioo (-1 : Real) 1) :
    profilePlanarDiffeomorph hρ H a R t ht '' closedBall (0 : E2) 1 =
      horizontal '' ((profileCapShear hρ H a R '' closedBall (0 : E3) 1) ∩ {y | y 2 = t}) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨profileCapShear hρ H a R (tangentPlanarLatitude t q), ⟨?_, ?_⟩,
      (profilePlanarDiffeomorph_apply hρ H a R t ht q).symm⟩
    · exact ⟨tangentPlanarLatitude t q,
        ((tangentPlanarLatitude_image_closedBall ht) ▸ mem_image_of_mem _ hq).1, rfl⟩
    · simp [tangentPlanarLatitude]
  · rintro ⟨p, ⟨⟨x, hx, rfl⟩, hxt⟩, rfl⟩
    have hh : x 2 = t := by
      change profileCapShear hρ H a R x 2 = t at hxt
      simpa only [profileCapShear_two] using hxt
    obtain ⟨q, hq, hqe⟩ := (tangentPlanarLatitude_image_closedBall ht).symm ▸
      (show x ∈ closedBall (0 : E3) 1 ∩ {y | y 2 = t} from ⟨hx, hh⟩)
    refine ⟨q, hq, ?_⟩
    rw [profilePlanarDiffeomorph_apply, hqe]

theorem profilePlanarDiffeomorph_sphere {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R t : Real) (ht : t ∈ Ioo (-1 : Real) 1) :
    profilePlanarDiffeomorph hρ H a R t ht '' sphere (0 : E2) 1 =
      horizontal '' ((profileCapShear hρ H a R '' sphere (0 : E3) 1) ∩ {y | y 2 = t}) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨profileCapShear hρ H a R (tangentPlanarLatitude t q), ⟨?_, ?_⟩,
      (profilePlanarDiffeomorph_apply hρ H a R t ht q).symm⟩
    · exact ⟨tangentPlanarLatitude t q, sphereLatitude_mem_sphere ht ⟨q, hq⟩, rfl⟩
    · simp [tangentPlanarLatitude]
  · rintro ⟨p, ⟨⟨x, hx, rfl⟩, hxt⟩, rfl⟩
    have hh : x 2 = t := by
      change profileCapShear hρ H a R x 2 = t at hxt
      simpa only [profileCapShear_two] using hxt
    obtain ⟨q, hq⟩ := (range_sphereLatitude ht).symm ▸
      (show x ∈ sphere (0 : E3) 1 ∩ {y | y 2 = t} from ⟨hx, hh⟩)
    refine ⟨q, q.property, ?_⟩
    rw [profilePlanarDiffeomorph_apply]
    exact congrArg (horizontal ∘ profileCapShear hρ H a R) hq

theorem mem_profilePlanarDiffeomorph_image_iff {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R t : Real)
    (ht : t ∈ Ioo (-1 : Real) 1) (S : Set E2) (p : E2) :
    p ∈ profilePlanarDiffeomorph hρ H a R t ht '' S ↔
      planarGraphFlattening (contDiff_profilePlanarDisplacement hρ H a R t) p ∈
        tangentPlanarDiffeomorph t ht '' S := by
  let D := planarGraphFlattening (contDiff_profilePlanarDisplacement hρ H a R t)
  have he (q : E2) : D (profilePlanarDiffeomorph hρ H a R t ht q) =
      tangentPlanarDiffeomorph t ht q := D.apply_symm_apply _
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, hq, (he q).symm.trans (congrArg D hqp)⟩
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, hq, D.injective ((he q).trans hqp)⟩

theorem profilePlanarDiffeomorph_body_graph_bound {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R t : Real)
    (ht : t ∈ Ioo (-1 : Real) 1) {p : E2}
    (hp : p ∈ profilePlanarDiffeomorph hρ H a R t ht '' closedBall (0 : E2) 1) :
    p 0 ≤ profilePlanarDisplacement ρ H a R t (p 1) := by
  have hm := (mem_profilePlanarDiffeomorph_image_iff hρ H a R t ht
    (closedBall (0 : E2) 1) p).mp hp
  have hbound := tangentPlanarDiffeomorph_body_nonpos ht hm
  rw [planarGraphFlattening_zero] at hbound
  exact sub_nonpos.mp hbound

theorem profilePlanarDiffeomorph_sphere_graph_bound {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R t : Real)
    (ht : t ∈ Ioo (-1 : Real) 1) {p : E2}
    (hp : p ∈ profilePlanarDiffeomorph hρ H a R t ht '' sphere (0 : E2) 1) :
    p 0 ≤ profilePlanarDisplacement ρ H a R t (p 1) :=
  profilePlanarDiffeomorph_body_graph_bound hρ H a R t ht
    (image_mono sphere_subset_closedBall hp)



theorem profilePlanarDiffeomorph_graph_germ {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R t : Real)
    (ht : t ∈ Ioo (-1 : Real) 1) {p : E2}
    (hpgraph : p 0 = profilePlanarDisplacement ρ H a R t (p 1))
    (hp : (p 1) ^ 2 + t ^ 2 < 1 / 4) :
    ∀ᶠ y in 𝓝 p, y ∈ profilePlanarDiffeomorph hρ H a R t ht '' sphere (0 : E2) 1 ↔
      y 0 = profilePlanarDisplacement ρ H a R t (y 1) := by
  let D := planarGraphFlattening (contDiff_profilePlanarDisplacement hρ H a R t)
  have hDzero : D p 0 = 0 := by
    change planarGraphFlattening (contDiff_profilePlanarDisplacement hρ H a R t) p 0 = 0
    rw [planarGraphFlattening_zero, hpgraph, sub_self]
  have hDsmall : (D p 1) ^ 2 + t ^ 2 < 1 / 4 := by
    simpa only [D, planarGraphFlattening_one] using hp
  have hgerm := tangentPlanarDiffeomorph_wall_germ ht hDzero hDsmall
  filter_upwards [D.continuous.continuousAt.eventually hgerm] with y hy
  rw [← mem_profilePlanarDiffeomorph_image_iff hρ H a R t ht (sphere (0 : E2) 1) y] at hy
  exact hy.trans (by
    change planarGraphFlattening (contDiff_profilePlanarDisplacement hρ H a R t) y 0 = 0 ↔ _
    rw [planarGraphFlattening_zero, sub_eq_zero])

theorem profilePlanarDiffeomorph_closing_graph_germ {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R y : Real)
    (hy : |y| < 1 / 2) :
    ∀ᶠ p in 𝓝 (WithLp.toLp 2 ![profileX ρ (H.symm (a + R ^ 2 - y ^ 2)), y] : E2),
      p ∈ profilePlanarDiffeomorph hρ H a R 0 (by constructor <;> norm_num) ''
        sphere (0 : E2) 1 ↔ p 0 = profileX ρ (H.symm (a + R ^ 2 - (p 1) ^ 2)) := by
  have hysq : y ^ 2 < 1 / 4 := by
    obtain ⟨hyl, hyr⟩ := abs_lt.mp hy
    nlinarith
  simpa only [profilePlanarDisplacement, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
    profilePlanarDiffeomorph_graph_germ hρ H a R 0 (by constructor <;> norm_num)
      (p := WithLp.toLp 2 ![profileX ρ (H.symm (a + R ^ 2 - y ^ 2)), y])
      (by simp [profilePlanarDisplacement]) (by simpa using hysq)

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
