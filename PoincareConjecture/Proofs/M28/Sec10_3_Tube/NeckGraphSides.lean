import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphIsotopy
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereCrossings
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar











noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



def neckGraphHeight (N : EpsilonNeck g) (f : UnitTwoSphere → ℝ) (x : M) : ℝ :=
  (N.coordinate_inverse x).2 - f (N.coordinate_inverse x).1



theorem continuousOn_neckGraphHeight (N : EpsilonNeck g)
    {f : UnitTwoSphere → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn (neckGraphHeight N f) N.carrier :=
  (continuous_snd.comp_continuousOn N.coordinate_inverse_smooth.continuousOn).sub
    (hf.continuous.comp_continuousOn
      (continuous_fst.comp_continuousOn N.coordinate_inverse_smooth.continuousOn))



theorem neckGraphHeight_coordinate_map (N : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (p : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    neckGraphHeight N f (N.coordinate_map (p, s)) = s - f p := by
  unfold neckGraphHeight
  rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]



theorem neckGraphHeight_eq_zero_iff (N : EpsilonNeck g)
    {f : UnitTwoSphere → ℝ}
    (hdom : ∀ p, f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {x : M} (hx : x ∈ N.carrier) :
    neckGraphHeight N f x = 0 ↔
      x ∈ range (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
  constructor
  · intro hz
    have heq : (N.coordinate_inverse x).2 = f (N.coordinate_inverse x).1 :=
      sub_eq_zero.mp hz
    refine ⟨(N.coordinate_inverse x).1, ?_⟩
    change N.coordinate_map ((N.coordinate_inverse x).1, f (N.coordinate_inverse x).1) = x
    rw [← heq]
    exact N.coordinate_map_coordinate_inverse hx
  · rintro ⟨p, rfl⟩
    rw [neckGraphHeight_coordinate_map N f p (hdom p), sub_self]



theorem neckGraphHeight_sides (N : EpsilonNeck g)
    {f : UnitTwoSphere → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ p, f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    IsOpen (N.carrier ∩ neckGraphHeight N f ⁻¹' Iio 0) ∧
    IsOpen (N.carrier ∩ neckGraphHeight N f ⁻¹' Ioi 0) ∧
    Disjoint (N.carrier ∩ neckGraphHeight N f ⁻¹' Iio 0)
      (N.carrier ∩ neckGraphHeight N f ⁻¹' Ioi 0) ∧
    (N.carrier ∩ neckGraphHeight N f ⁻¹' Iio 0) ∪
        (N.carrier ∩ neckGraphHeight N f ⁻¹' Ioi 0) =
      N.carrier \ range (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
  have hq := continuousOn_neckGraphHeight N hf
  refine ⟨hq.isOpen_inter_preimage N.carrier_open isOpen_Iio,
    hq.isOpen_inter_preimage N.carrier_open isOpen_Ioi, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hx hy
    have hn : neckGraphHeight N f x < 0 := hx.2
    have hp : 0 < neckGraphHeight N f x := hy.2
    exact (not_lt_of_ge hn.le) hp
  · ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, fun hz => (ne_of_lt hx.2)
          ((neckGraphHeight_eq_zero_iff N hdom hx.1).mpr hz)⟩
      · exact ⟨hx.1, fun hz => (ne_of_gt hx.2)
          ((neckGraphHeight_eq_zero_iff N hdom hx.1).mpr hz)⟩
    · rintro ⟨hx, hxS⟩
      have hne : neckGraphHeight N f x ≠ 0 :=
        fun hz => hxS ((neckGraphHeight_eq_zero_iff N hdom hx).mp hz)
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact Or.inl ⟨hx, hneg⟩
      · exact Or.inr ⟨hx, hpos⟩




theorem exists_neckGraphHeight_negative_in_open (N : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) {T : Set M} (hT : IsOpen T)
    (p : UnitTwoSphere) (hp : N.coordinate_map (p, f p) ∈ T)
    (hdom : f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {kappa : ℝ} (hkappa : kappa = 1 ∨ kappa = -1) :
    ∃ y ∈ T, y ∈ N.carrier ∧ kappa * neckGraphHeight N f y < 0 := by
  let z : ℝ → RoundCylinderSpace := fun t => (p, f p - kappa * t)
  let curve : ℝ → M := N.coordinate_map ∘ z
  have hz : Continuous z :=
    continuous_const.prodMk (continuous_const.sub (continuous_const.mul continuous_id))
  have hz0 : z 0 ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    change p ∈ univ ∧ f p - kappa * 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    simpa only [mul_zero, sub_zero] using And.intro (mem_univ p) hdom
  have hcurve : ContinuousAt curve 0 :=
    (N.coordinate_map_smooth.continuousOn.continuousAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz0)).comp hz.continuousAt
  have hcurve0 : curve 0 ∈ T := by
    simpa only [curve, Function.comp_apply, z, mul_zero, sub_zero] using hp
  have hW : {t : ℝ | z t ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧ curve t ∈ T}
      ∈ 𝓝 (0 : ℝ) :=
    inter_mem (hz.continuousAt.preimage_mem_nhds
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz0))
      (hcurve.preimage_mem_nhds (hT.mem_nhds hcurve0))
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hW
  have ht : delta / 2 ∈ Metric.ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hstrip, hmem⟩ := hball ht
  refine ⟨curve (delta / 2), hmem, N.coordinate_map_mem hstrip, ?_⟩
  change kappa * neckGraphHeight N f (N.coordinate_map (p, f p - kappa * (delta / 2))) < 0
  rw [neckGraphHeight_coordinate_map N f p hstrip.2]
  dsimp only [z]
  rcases hkappa with rfl | rfl <;> nlinarith



theorem exists_neck_graph_crossing (N : EpsilonNeck g)
    {f : UnitTwoSphere → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ p, f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hγN : MapsTo γ (Icc a b) N.carrier)
    {kappa : ℝ} (hkappa : kappa = 1 ∨ kappa = -1)
    (ha : kappa * neckGraphHeight N f (γ a) < 0)
    (hb : 0 < kappa * neckGraphHeight N f (γ b)) :
    ∃ t ∈ Ioo a b,
      γ t ∈ range (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
  apply exists_sphere_crossing_of_signed_height
    (continuousOn_const.mul (continuousOn_neckGraphHeight N hf)) ?_ hab hγ hγN ha hb
  intro x hx
  have hne : kappa ≠ 0 := by rcases hkappa with rfl | rfl <;> norm_num
  change kappa * neckGraphHeight N f x = 0 ↔
    x ∈ range (fun p : UnitTwoSphere => N.coordinate_map (p, f p))
  rw [mul_eq_zero, or_iff_right hne]
  exact neckGraphHeight_eq_zero_iff N hdom hx

end PoincareConjecture.M28
