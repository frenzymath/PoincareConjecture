import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeFreshSlab
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PathCrossingDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereCrossings
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallRetainedPath










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28

namespace SourceTubeData

variable {epsilon C A D0 D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D0 D}
  {S : CounterexampleNeckSegment E}




theorem intrinsic_edist_add_le_of_fresh_sphere_height (T : SourceTubeData S)
    (hsmall : epsilon ≤ (1 / 10000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    (N : EpsilonNeck (E.flow.metric E.time)) (heps : N.epsilon = epsilon)
    (hscale : N.scale ≤ (101 / 100 : ℝ) * (T.list.node 0).2.scale)
    (hterminal : Disjoint N.carrier
      (closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)))
    (b p x : T.carrierOpen) (hx : x.val ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x.val).2| ≤ 3 * epsilon⁻¹ / 4)
    (hp : p.val ∉ N.carrier)
    (hside : ∀ y ∈ N.central_sphere, y ∉ (T.list.node 0).2.belowGraph_m28 f)
    (height : T.carrierOpen → ℝ) (hcont : Continuous height)
    (hzero : ∀ y : T.carrierOpen, height y = 0 ↔ y.val ∈ N.central_sphere)
    (hbneg : height b < 0) (hppos : 0 < height p) :
    (intrinsicOpenMetric (E.flow.metric E.time) T.carrierOpen).edist b x +
      ENNReal.ofReal (N.scale * epsilon⁻¹ / 8) ≤
        (intrinsicOpenMetric (E.flow.metric E.time) T.carrierOpen).edist b p := by
  have hepspos : 0 < epsilon := heps ▸ N.epsilon_pos
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr hepspos
  have hN := N.scale_pos
  have hroot : (999 / 1000 : ℝ) ≤ Real.sqrt (1 - epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - epsilon)]
  apply (intrinsicOpenMetric (E.flow.metric E.time) T.carrierOpen).edist_add_le_of_path_crossing
    (S := {y : T.carrierOpen | y.val ∈ N.central_sphere})
    (c := ENNReal.ofReal ((151 / 200 : ℝ) * N.scale * epsilon⁻¹))
    (e := ENNReal.ofReal ((998001 / 1000000 : ℝ) * N.scale * epsilon⁻¹))
    ENNReal.ofReal_ne_top
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [mul_pos hN hA]
  · intro gamma h0 h1 hgamma
    obtain ⟨t, ht, hmem⟩ := exists_sphere_crossing_of_signed_height
      (U := univ) hcont.continuousOn (fun y _ => hzero y) zero_le_one
      hgamma.continuousOn (mapsTo_univ _ _) (by rwa [h0]) (by rwa [h1])
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, hmem⟩
  · intro y hy
    let w : ℝ := (999 / 1000 : ℝ) * epsilon⁻¹
    have hw : 0 < w := mul_pos (by norm_num) hA
    have hwA : w < N.epsilon⁻¹ := by rw [heps]; dsimp only [w]; linarith
    have hnot : p.val ∉ N.region (-w) w := fun hmem => hp hmem.1
    have hambient := N.edist_central_lower_of_not_mem_region hw hwA hy hnot
    rw [heps] at hambient
    have hcost : (998001 / 1000000 : ℝ) * N.scale * epsilon⁻¹ ≤
        (N.scale * Real.sqrt (1 - epsilon)) * w := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot hN.le) hw.le
      dsimp only [w] at hh ⊢
      nlinarith only [hh]
    rw [intrinsicOpenMetric_edist]
    exact ((ENNReal.ofReal_le_ofReal hcost).trans hambient).trans
      (RiemannianMetric.edist_le_intrinsicEDist (E.flow.metric E.time)
        (T.carrierOpen : Set _) y.val p.val)
  · intro y hy
    obtain ⟨gamma, h0, h1, hgamma, _, hgammaT, hlength⟩ :=
      T.exists_central_slab_competitor_in_tube hsmall f hf hbound N heps hscale
        hy y.property (hside y.val hy) hterminal hx hheight
    have hd := intrinsicEDist_le_pathELength (E.flow.metric E.time)
      zero_le_one hgamma hgammaT
    rw [h0, h1] at hd
    rw [intrinsicOpenMetric_edist]
    exact (hd.trans_lt hlength).le

end SourceTubeData

namespace CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}




theorem tube_edist_add_le_of_fresh_sphere_height
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    (k : ℕ) (hsmall : epsilon ≤ (1 / 10000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (heps : N.epsilon = epsilon)
    (hscale : N.scale ≤ (101 / 100 : ℝ) * ((T k).list.node 0).2.scale)
    (hterminal : Disjoint N.carrier
      (closure (((T k).list.node (((T k).list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)))
    (p x : (T k).carrierOpen) (hx : x.val ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x.val).2| ≤ 3 * epsilon⁻¹ / 4)
    (hp : p.val ∉ N.carrier)
    (hside : ∀ y ∈ N.central_sphere, y ∉ ((T k).list.node 0).2.belowGraph_m28 f)
    (height : (T k).carrierOpen → ℝ) (hcont : Continuous height)
    (hzero : ∀ y : (T k).carrierOpen, height y = 0 ↔ y.val ∈ N.central_sphere)
    (hbneg : height (H.tubeBase T k) < 0) (hppos : 0 < height p) :
    (H.tubeMetric T k).edist (H.tubeBase T k) x +
      ENNReal.ofReal (Real.sqrt ((E (k + H.shift)).flow.scalar
        ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) *
          N.scale * epsilon⁻¹ / 8) ≤
        (H.tubeMetric T k).edist (H.tubeBase T k) p := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hh := (T k).intrinsic_edist_add_le_of_fresh_sphere_height
    hsmall f hf hbound N heps hscale hterminal (H.tubeBase T k) p x hx hheight
    hp hside height hcont hzero hbneg hppos
  rw [intrinsicOpenMetric_edist, intrinsicOpenMetric_edist] at hh
  rw [tubeMetric, intrinsicOpenMetric_edist, intrinsicOpenMetric_edist,
    H.normalizedSlice_intrinsicEDist, H.normalizedSlice_intrinsicEDist]
  have hfactor : ENNReal.ofReal (Real.sqrt Q * N.scale * epsilon⁻¹ / 8) =
      ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal (N.scale * epsilon⁻¹ / 8) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    congr 1
    ring
  change ENNReal.ofReal (Real.sqrt Q) * _ +
    ENNReal.ofReal (Real.sqrt Q * N.scale * epsilon⁻¹ / 8) ≤
      ENNReal.ofReal (Real.sqrt Q) * _
  rw [hfactor, ← mul_add]
  exact mul_le_mul_right hh _

end CounterexampleNeckFamily

end PoincareConjecture.M28
