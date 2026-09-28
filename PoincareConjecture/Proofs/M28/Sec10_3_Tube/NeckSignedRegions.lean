import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



def neckSignedRegion (N : EpsilonNeck g) (sigma a b : ℝ) : Set M :=
  {x | x ∈ N.carrier ∧ a < sigma * (N.coordinate_inverse x).2 ∧
    sigma * (N.coordinate_inverse x).2 < b}


theorem neckSignedRegion_one (N : EpsilonNeck g) (a b : ℝ) :
    neckSignedRegion N 1 a b = N.region a b := by
  ext x
  simp only [neckSignedRegion, EpsilonNeck.region, mem_ofPred_eq, one_mul]


theorem neckSignedRegion_neg_one (N : EpsilonNeck g) (a b : ℝ) :
    neckSignedRegion N (-1) a b = N.region (-b) (-a) := by
  ext x
  simp only [neckSignedRegion, EpsilonNeck.region, mem_ofPred_eq, neg_one_mul,
    lt_neg, neg_lt]
  exact ⟨fun h => ⟨h.1, h.2.2, h.2.1⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩


theorem neck_signed_axis_mem (N : EpsilonNeck g) {sigma : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1) {x : M} (hx : x ∈ N.carrier) :
    sigma * (N.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have h := (N.coordinate_inverse_mem x hx).2
  rcases hsigma with rfl | rfl
  · simpa only [one_mul] using h
  · constructor <;> nlinarith [h.1, h.2]


theorem isOpen_neckSignedRegion (N : EpsilonNeck g) (sigma a b : ℝ) :
    IsOpen (neckSignedRegion N sigma a b) := by
  have h : ContinuousOn (fun x => sigma * (N.coordinate_inverse x).2) N.carrier :=
    continuousOn_const.mul
      (continuous_snd.comp_continuousOn N.coordinate_inverse_smooth.continuousOn)
  exact h.isOpen_inter_preimage N.carrier_open isOpen_Ioo



theorem isPreconnected_neckSignedRegion (N : EpsilonNeck g) {sigma a b : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) :
    IsPreconnected (neckSignedRegion N sigma a b) := by
  rcases hsigma with rfl | rfl
  · rw [neckSignedRegion_one]
    exact N.isPreconnected_region ha hb
  · rw [neckSignedRegion_neg_one]
    exact N.isPreconnected_region (by linarith) (by linarith)



theorem mem_neck_slice_iff_signed_axis (N : EpsilonNeck g) {sigma a : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (ha : sigma * a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {x : M} (hx : x ∈ N.carrier) :
    x ∈ range (fun p : UnitTwoSphere => N.coordinate_map (p, sigma * a)) ↔
      sigma * (N.coordinate_inverse x).2 = a := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, ha⟩]
    rcases hsigma with rfl | rfl <;> ring
  · intro heq
    have haxis : (N.coordinate_inverse x).2 = sigma * a := by
      rcases hsigma with rfl | rfl <;> nlinarith
    refine ⟨(N.coordinate_inverse x).1, ?_⟩
    rw [← haxis]
    exact N.coordinate_map_coordinate_inverse hx

end PoincareConjecture.M28
