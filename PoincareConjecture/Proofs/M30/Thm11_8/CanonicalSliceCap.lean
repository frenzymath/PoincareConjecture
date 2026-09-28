import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapRecutBoundary
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.RecutDiameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import Mathlib.Topology.OpenPartialHomeomorph.IsImage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M30




theorem exists_cap_side_of_inverse_neck_coordinates
    {M : Type v} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {X : Type u} [TopologicalSpace X] [T3Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X]
    [MeasurableSpace X] [BorelSpace X]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 X)
    (A : CapCertificate h)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hcapture : A.carrier ⊆ e.target)
    (V : EpsilonNeck g) (hepsilon : A.epsilon ≤ V.epsilon)
    (hcoord : V.coordinate_map = e.symm ∘ A.end_neck.coordinate_map)
    {x : M} (hx : x ∈ e.source) (hcore : e x ∈ A.core)
    {L b : ℝ} (hL : 0 < L) (_hb : 0 < b)
    (hbound : ∀ z ∈ A.carrier, ∀ w : TangentSpace (𝓡 3) z,
      g.tangentNorm (e.symm z)
          (mfderiv (𝓡 3) (𝓡 3) e.symm z w) ≤
        L * h.tangentNorm z w)
    (hradius : ∀ z ∈ A.carrier,
      intrinsicEDist h A.carrier (e x) z < ENNReal.ofReal b) :
    ∃ W : Set M,
      IsOpen W ∧ IsCompact (closure W) ∧ x ∈ W ∧ x ∉ V.carrier ∧
      frontier W = V.central_sphere ∧
      W ∩ V.carrier = V.region (-V.epsilon⁻¹) 0 ∧
      closure W ⊆ g.ball x (L * b) := by
  have hleft (z : M) (hz : z ∈ e.source) : e.symm (e z) = z := e.left_inv hz
  have hright (z : X) (hz : z ∈ e.target) : e (e.symm z) = z := e.right_inv hz
  let W0 := A.closed_core ∪ A.end_neck.region (-A.epsilon⁻¹) 0
  let W := e.symm '' W0
  have hnegative : -A.epsilon⁻¹ < (0 : ℝ) := neg_neg_of_pos (inv_pos.mpr A.epsilon_pos)
  have hpositive : (0 : ℝ) < A.epsilon⁻¹ := inv_pos.mpr A.epsilon_pos
  obtain ⟨hW0open, hW0compact, hW0cap⟩ := A.open_precompact_recut hnegative hpositive
  have hW0target : closure W0 ⊆ e.target := hW0cap.trans hcapture
  have hWsource : W ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (hW0target (subset_closure hz))
  have hWopen : IsOpen W :=
    e.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target hW0open
      (subset_closure.trans hW0target)
  have hclosedImage : IsCompact (e.symm '' closure W0) :=
    hW0compact.image_of_continuousOn (e.contMDiffOn_invFun.continuousOn.mono hW0target)
  have hclosureSub : closure W ⊆ e.symm '' closure W0 :=
    closure_minimal (image_mono subset_closure) hclosedImage.isClosed
  have hclosureSource : closure W ⊆ e.source := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hclosureSub hz
    exact e.map_target (hW0target hw)
  have himage : e.toOpenPartialHomeomorph.IsImage W W0 := by
    intro z hz
    constructor
    · intro hez
      exact ⟨e z, hez, e.left_inv hz⟩
    · rintro ⟨w, hw, rfl⟩
      change e (e.symm w) ∈ W0
      rwa [hright w (hW0target (subset_closure hw))]
  have hclosure : closure W = e.symm '' closure W0 := by
    have hh := himage.symm.closure.image_eq
    change e.symm '' (e.target ∩ closure W0) = e.source ∩ closure W at hh
    rw [inter_eq_right.mpr hW0target, inter_eq_right.mpr hclosureSource] at hh
    exact hh.symm
  have hfrontier : frontier W = e.symm '' frontier W0 := by
    have hh := himage.symm.frontier.image_eq
    change e.symm '' (e.target ∩ frontier W0) = e.source ∩ frontier W at hh
    rw [inter_eq_right.mpr (frontier_subset_closure.trans hW0target),
      inter_eq_right.mpr (frontier_subset_closure.trans hclosureSource)] at hh
    exact hh.symm
  have hfrontierV : frontier W = V.central_sphere := by
    rw [hfrontier, A.frontier_innerRecut hnegative hpositive,
      V.central_sphere_eq, hcoord, image_comp]
  have hcoreClosed : e x ∈ A.closed_core :=
    interior_subset (A.core_eq_interior_closed_core ▸ hcore)
  have hxW : x ∈ W := ⟨e x, Or.inl hcoreClosed, e.left_inv hx⟩
  have haxis {z : UnitTwoSphere × ℝ}
      (hz : z.2 ∈ Ioo (-V.epsilon⁻¹) V.epsilon⁻¹) :
      z.2 ∈ Ioo (-A.end_neck.epsilon⁻¹) A.end_neck.epsilon⁻¹ := by
    have hinv := inv_anti₀ A.epsilon_pos hepsilon
    rw [A.end_neck_epsilon]
    exact ⟨(neg_le_neg hinv).trans_lt hz.1, hz.2.trans_le hinv⟩
  have hVdata (z : M) (hz : z ∈ V.carrier) :
      z ∈ e.source ∧ e z ∈ A.end_neck.carrier ∧
        A.end_neck.coordinate_inverse (e z) = V.coordinate_inverse z := by
    let w := V.coordinate_inverse z
    have hw := haxis (V.coordinate_inverse_mem z hz).2
    have hwEnd := A.end_neck.coordinate_map_mem_of_axial w hw
    have hwTarget := hcapture (A.end_neck_subset hwEnd)
    have hzeq : z = e.symm (A.end_neck.coordinate_map w) := by
      have hh := congrFun hcoord w
      rwa [V.coordinate_map_coordinate_inverse hz] at hh
    have hez : e z = A.end_neck.coordinate_map w := by
      rw [hzeq, hright _ hwTarget]
    refine ⟨hzeq.symm ▸ e.map_target hwTarget, hez.symm ▸ hwEnd, ?_⟩
    rw [hez, A.end_neck.coordinate_inverse_coordinate_map_of_axial w hw]
  have hxNot : x ∉ V.carrier := by
    intro hxV
    have hnot := (A.closed_core_eq_complement_end ▸ hcoreClosed).2
    exact hnot (hVdata x hxV).2.1
  have hoverlap : W ∩ V.carrier = V.region (-V.epsilon⁻¹) 0 := by
    ext z
    constructor
    · rintro ⟨hzW, hzV⟩
      obtain ⟨hzsource, hzEnd, hinv⟩ := hVdata z hzV
      have hmem := (himage hzsource).mpr hzW
      change e z ∈ W0 at hmem
      rcases hmem with hzcore | hzinner
      · exact False.elim ((A.closed_core_eq_complement_end ▸ hzcore).2 hzEnd)
      · refine ⟨hzV, (V.coordinate_inverse_mem z hzV).2.1, ?_⟩
        simpa only [hinv] using hzinner.2.2
    · intro hz
      obtain ⟨hzsource, hzEnd, hinv⟩ := hVdata z hz.1
      refine ⟨(himage hzsource).mp ?_, hz.1⟩
      change e z ∈ W0
      refine Or.inr ⟨hzEnd, ?_, ?_⟩
      · simpa only [A.end_neck_epsilon] using
          (A.end_neck.coordinate_inverse_mem (e z) hzEnd).2.1
      · simpa only [hinv] using hz.2.2
  let eH := e.toOpenPartialHomeomorph.symm.restrOpen A.carrier A.carrier_open
  let eA : PartialDiffeomorph (𝓡 3) (𝓡 3) X M ∞ :=
    { toPartialEquiv := eH.toPartialEquiv
      open_source := eH.open_source
      open_target := eH.open_target
      contMDiffOn_toFun := e.contMDiffOn_invFun.mono inter_subset_left
      contMDiffOn_invFun := e.contMDiffOn_toFun.mono inter_subset_left }
  have hsourceA : eA.source = A.carrier := inter_eq_right.mpr hcapture
  have hboundA (z : X) (hz : z ∈ eA.source) (w : TangentSpace (𝓡 3) z) :
      g.tangentNorm (eA z) (mfderiv (𝓡 3) (𝓡 3) eA z w) ≤
        L * h.tangentNorm z w := by
    exact hbound z (hsourceA ▸ hz) w
  refine ⟨W, hWopen, hclosure.symm ▸ hclosedImage, hxW, hxNot, hfrontierV, hoverlap, ?_⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hclosureSub hz
  have hd := CapRecut.intrinsicEDist_le_mul_of_differential_bound h g eA hL hboundA (e x) w
  change intrinsicEDist g eA.target (e.symm (e x)) (e.symm w) ≤
    ENNReal.ofReal L * intrinsicEDist h eA.source (e x) w at hd
  rw [hleft x hx, hsourceA] at hd
  change g.edist x (e.symm w) < ENNReal.ofReal (L * b)
  apply ((g.edist_le_intrinsicEDist eA.target x (e.symm w)).trans hd).trans_lt
  rw [ENNReal.ofReal_mul hL.le]
  exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hL).ne'
    ENNReal.ofReal_ne_top (hradius w (hW0cap hw))

end PoincareConjecture.M30
