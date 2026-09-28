import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InteriorCapture
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialMonotonicity













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

private theorem barrier_bounds {R B n q : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hn : n ∈ Ioo (-R / 2) R) (hq : q ∈ Ioo (-R) (R / 2))
    (hpos : R / 2 < n → -(3 / 4 : ℝ) * R ≤ q)
    (hneg : q < -R / 2 → n ≤ (0.6 : ℝ) * R)
    (hbound : |(R - n)⁻¹ - (R + q)⁻¹| ≤ B) :
    n ≤ R - (B + 10 / R)⁻¹ ∧ -R + (B + 10 / R)⁻¹ ≤ q := by
  have hD : 0 < B + 10 / R := by positivity
  have hδ : (B + 10 / R)⁻¹ ≤ R / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hD]
    have hten : (10 / R) * (R / 2) = 5 := by field_simp; ring
    nlinarith [mul_nonneg hB (half_pos hR).le]
  have hnpos : 0 < R - n := sub_pos.mpr hn.2
  have hqpos : 0 < R + q := by linarith [hq.1]
  constructor
  · by_cases hnlow : n ≤ R / 2
    · linarith
    · have hqfour : R / 4 ≤ R + q := by
        have h := hpos (lt_of_not_ge hnlow)
        linarith
      have hinv : (R + q)⁻¹ ≤ 4 / R := by
        calc
          _ ≤ (R / 4)⁻¹ := inv_anti₀ (by positivity) hqfour
          _ = _ := by field_simp
      have hden : (R - n)⁻¹ ≤ B + 10 / R := by
        have h := (abs_le.mp hbound).2
        have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
        simp only [div_eq_mul_inv] at hinv ⊢
        nlinarith
      have hmargin := (inv_le_comm₀ hD hnpos).mpr hden
      linarith
  · by_cases hqhigh : -R / 2 ≤ q
    · linarith
    · have hnfive : (2 / 5 : ℝ) * R ≤ R - n := by
        have h := hneg (lt_of_not_ge hqhigh)
        linarith
      have hinv : (R - n)⁻¹ ≤ (5 / 2 : ℝ) / R := by
        calc
          _ ≤ ((2 / 5 : ℝ) * R)⁻¹ := inv_anti₀ (by positivity) hnfive
          _ = _ := by field_simp
      have hden : (R + q)⁻¹ ≤ B + 10 / R := by
        have h := (abs_le.mp hbound).1
        have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
        simp only [div_eq_mul_inv] at hinv ⊢
        nlinarith
      have hmargin := (inv_le_comm₀ hD hqpos).mpr hden
      linarith

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}


noncomputable def overlapBarrier (N Q : EpsilonNeck g) (x : M) : ℝ :=
  (N.epsilon⁻¹ - (N.coordinate_inverse x).2)⁻¹ -
    (Q.epsilon⁻¹ + (Q.coordinate_inverse x).2)⁻¹

theorem overlapBarrier_continuousOn (N Q : EpsilonNeck g) :
    ContinuousOn (N.overlapBarrier Q) (N.carrier ∩ Q.carrier) := by
  have hN : ContinuousOn (fun x => (N.coordinate_inverse x).2) (N.carrier ∩ Q.carrier) :=
    N.coordinate_inverse_smooth.continuousOn.snd.mono inter_subset_left
  have hQ : ContinuousOn (fun x => (Q.coordinate_inverse x).2) (N.carrier ∩ Q.carrier) :=
    Q.coordinate_inverse_smooth.continuousOn.snd.mono inter_subset_right
  apply ((continuousOn_const.sub hN).inv₀ ?_).sub ((continuousOn_const.add hQ).inv₀ ?_)
  · intro x hx
    exact sub_ne_zero.mpr (ne_of_gt (N.coordinate_inverse_mem x hx.1).2.2)
  · intro x hx
    have h := (Q.coordinate_inverse_mem x hx.2).2.1
    change Q.epsilon⁻¹ + (Q.coordinate_inverse x).2 ≠ 0
    linarith



theorem isCompact_overlapBarrier_band [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] (N Q : EpsilonNeck g)
    (heq : Q.epsilon = N.epsilon)
    (hoverlap : N.carrier ∩ Q.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2))
    (hpositive : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      Q.coordinate_map '' (univ ×ˢ
        Icc (-(3 / 4 : ℝ) * N.epsilon⁻¹) ((3 / 4 : ℝ) * N.epsilon⁻¹)))
    (hnegative : Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
      N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹))
    (B : ℝ) (hB : 0 ≤ B) :
    IsCompact {x | x ∈ N.carrier ∩ Q.carrier ∧ |N.overlapBarrier Q x| ≤ B} := by
  let R := N.epsilon⁻¹
  let δ := (B + 10 / R)⁻¹
  have hR : 0 < R := inv_pos.mpr N.epsilon_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hNlo : -N.epsilon⁻¹ < -R / 2 := by change -R < -R / 2; linarith
  have hNhi : R - δ < N.epsilon⁻¹ := by change R - δ < R; linarith
  have hQlo : -Q.epsilon⁻¹ < -R + δ := by rw [heq]; change -R < -R + δ; linarith
  have hQhi : R / 2 < Q.epsilon⁻¹ := by rw [heq]; change R / 2 < R; linarith
  let K := N.coordinate_map '' (univ ×ˢ Icc (-R / 2) (R - δ))
  let L := Q.coordinate_map '' (univ ×ˢ Icc (-R + δ) (R / 2))
  let A := {x | x ∈ N.carrier ∩ Q.carrier ∧ |N.overlapBarrier Q x| ≤ B}
  have hK : IsCompact K := N.isCompact_coordinate_slab hNlo hNhi
  have hL : IsCompact L := Q.isCompact_coordinate_slab hQlo hQhi
  have hKL : K ∩ L ⊆ N.carrier ∩ Q.carrier :=
    inter_subset_inter (fun _ hx => ((N.mem_coordinate_slab_iff hNlo hNhi).mp hx).1)
      (fun _ hx => ((Q.mem_coordinate_slab_iff hQlo hQhi).mp hx).1)
  have hsub : A ⊆ K ∩ L := by
    rintro x ⟨hx, hbound⟩
    have hcoords := hoverlap hx
    have hb := barrier_bounds hR hB hcoords.1.2 hcoords.2.2
      (fun hn => by
        have hs := (Q.mem_coordinate_slab_iff
          (by rw [heq]; linarith [inv_pos.mpr N.epsilon_pos])
          (by rw [heq]; linarith [inv_pos.mpr N.epsilon_pos])).mp
          (hpositive ⟨hx.1, hn, hcoords.1.2.2⟩)
        exact hs.2.1)
      (fun hq => (hnegative ⟨hx.2, hcoords.2.2.1, hq⟩).2.2.le)
      (by simpa only [overlapBarrier, heq] using hbound)
    exact ⟨(N.mem_coordinate_slab_iff hNlo hNhi).mpr
      ⟨hx.1, hcoords.1.2.1.le, hb.1⟩,
      (Q.mem_coordinate_slab_iff hQlo hQhi).mpr
        ⟨hx.2, hb.2, hcoords.2.2.2.le⟩⟩
  have hclosure : closure A ⊆ N.carrier ∩ Q.carrier :=
    (closure_minimal hsub (hK.isClosed.inter hL.isClosed)).trans hKL
  have hclosed : IsClosed A := by
    have hcont := (N.overlapBarrier_continuousOn Q).abs.mono hclosure
    have hc := hcont.preimage_isClosed_of_isClosed isClosed_closure (isClosed_Iic (a := B))
    have heqA : A = closure A ∩ (fun x => |N.overlapBarrier Q x|) ⁻¹' Iic B := by
      ext x
      exact ⟨fun hx => ⟨subset_closure hx, hx.2⟩,
        fun hx => ⟨hclosure hx.1, hx.2⟩⟩
    exact heqA ▸ hc
  exact hK.of_isClosed_subset hclosed (hsub.trans inter_subset_left)

end PoincareConjecture.EpsilonNeck
