import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.TriangularHalfBalls

/-!
# A thin finite PL collar of a triangular boundary disk

Positive vertical scaling gives an explicit three-ball between
the flat triangle and a small roof cap. A scale below one keeps
it inside the original half-ball, meeting its other boundary
disk only on the rim. This is the local collar in Hudson 1969,
Lemma 2.14, pp. 60--61; see M76 derivation 247.
-/

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

/-- The closed tapered collar below a scaled triangular roof.
Only positive scales are used for its ball interpretation.
See Hudson Lemma 2.14 and M76 derivation 247. -/
def thinCollar (t : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ t * roof p.1}

/-- A positive thin collar is a finite PL three-ball whose
boundary is its exact scaled cap and flat disk. It is the
vertical affine image of the standard half-ball.
See Hudson pp. 60--61 and M76 derivation 247. -/
theorem isFinitePLBallPair_thinCollar {t : ℝ} (ht : 0 < t) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (thinCollar t) (cap t ∪ disk) := by
  let a : ((ℝ × ℝ) × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.prod
      (t • (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap)
  have hinj : InjOn a (halfBall 1) := by
    intro x _ y _ hxy
    change (x.1, t * x.2) = (y.1, t * y.2) at hxy
    have hfirst := congrArg (fun p : (ℝ × ℝ) × ℝ => p.1) hxy
    have hsecond := congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) hxy
    exact Prod.ext hfirst (mul_left_cancel₀ ht.ne' hsecond)
  have hcarrier : a '' halfBall 1 = thinCollar t := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 0 ≤ (1 : ℝ) * x.2 ∧ (1 : ℝ) * x.2 ≤ roof x.1 at hx
      simp only [one_mul] at hx
      change 0 ≤ t * x.2 ∧ t * x.2 ≤ t * roof x.1
      exact ⟨mul_nonneg ht.le hx.1, mul_le_mul_of_nonneg_left hx.2 ht.le⟩
    · intro hp
      change 0 ≤ p.2 ∧ p.2 ≤ t * roof p.1 at hp
      refine ⟨(p.1, p.2 / t), ?_, ?_⟩
      · change 0 ≤ (1 : ℝ) * (p.2 / t) ∧ (1 : ℝ) * (p.2 / t) ≤ roof p.1
        simp only [one_mul]
        exact ⟨div_nonneg hp.1 ht.le, (div_le_iff₀ ht).mpr (by simpa [mul_comm] using hp.2)⟩
      · apply Prod.ext
        · rfl
        · change t * (p.2 / t) = p.2
          field_simp [ht.ne']
  have hcap : a '' cap 1 = cap t := by
    rw [cap, image_image]
    apply image_congr
    intro x _
    apply Prod.ext
    · rfl
    · change t * ((1 : ℝ) * roof x) = t * roof x
      rw [one_mul]
  have hdisk : a '' disk = disk := by
    rw [disk, image_image]
    apply image_congr
    intro x _
    apply Prod.ext
    · rfl
    · change t * (0 : ℝ) = 0
      exact mul_zero t
  have hpair := (isFinitePLBallPair_halfBall (h := 1) (Or.inl rfl)).affine_image a hinj
  rwa [image_union, hcarrier, hcap, hdisk] at hpair

/-- A collar of scale at most one stays inside its parent
half-ball. See Hudson pp. 60--61 and M76 derivation 247. -/
theorem thinCollar_subset_halfBall {t : ℝ} (ht : 0 < t) (htone : t ≤ 1) :
    thinCollar t ⊆ halfBall 1 := by
  intro p hp
  change 0 ≤ p.2 ∧ p.2 ≤ t * roof p.1 at hp
  change 0 ≤ (1 : ℝ) * p.2 ∧ (1 : ℝ) * p.2 ≤ roof p.1
  simp only [one_mul]
  have hr : 0 ≤ roof p.1 := by nlinarith [hp.1, hp.2]
  exact ⟨hp.1, hp.2.trans (by nlinarith)⟩

/-- A strictly thinner collar meets the parent roof cap
exactly in their common triangular rim. See Hudson pp. 60--61
and M76 derivation 247. -/
theorem thinCollar_inter_cap {t : ℝ} (htone : t < 1) :
    thinCollar t ∩ cap 1 = rim := by
  ext p
  rw [mem_inter_iff, mem_cap, mem_rim]
  constructor
  · rintro ⟨hp, hb, hz⟩
    change 0 ≤ p.2 ∧ p.2 ≤ t * roof p.1 at hp
    simp only [one_mul] at hz
    have hr := (roof_nonneg_iff p.1).mpr hb
    have hrzero : roof p.1 = 0 := by nlinarith [hp.2]
    exact ⟨hrzero, hz.trans hrzero⟩
  · rintro ⟨hr, hz⟩
    have hb := (roof_nonneg_iff p.1).mp hr.ge
    exact ⟨by change 0 ≤ p.2 ∧ p.2 ≤ t * roof p.1; simp [hr, hz],
      hb, by simp [hr, hz]⟩

end TriangularRoofModel
