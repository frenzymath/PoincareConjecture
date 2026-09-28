


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.TransverseCuts
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.AdjacentStrips
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Convex.Segment








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves.TransverseCutCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {lo : ℝ → ℝ} {a u w : ℝ} (C : TransverseCutCoordinates lo a u w)

theorem parameter_Icc_subset_source {r : ℝ} (hr : r ∈ C.parameter.source) :
    Icc (0 : ℝ) r ⊆ C.parameter.source := by
  obtain ⟨l, hl, s, _, hs⟩ := C.source_interval
  rw [hs] at hr ⊢
  intro t ht
  exact ⟨hl.trans_le ht.1, ht.2.trans_lt hr.2⟩

theorem parameter_image_Icc {r : ℝ} (hr : 0 ≤ r) (hrs : r ∈ C.parameter.source) :
    C.parameter '' Icc (0 : ℝ) r = Icc (0 : ℝ) (C.parameter r) := by
  have hI := C.parameter_Icc_subset_source hrs
  simpa only [C.parameter_zero] using
    (C.parameter.continuousOn.mono hI).image_Icc_of_monotoneOn hr
      (C.strictMono.monotoneOn.mono hI)



theorem inverse_ray_image_Icc (p d : E) {r : ℝ} (hr : 0 ≤ r)
    (hrs : r ∈ C.parameter.source) :
    (fun z => p + C.parameter.symm z • d) '' Icc (0 : ℝ) (C.parameter r) =
      segment ℝ p (p + r • d) := by
  rw [← C.parameter_image_Icc hr hrs, image_image]
  calc
    _ = (fun t : ℝ => p + t • d) '' Icc (0 : ℝ) r := by
      apply image_congr
      intro t ht
      rw [C.parameter.left_inv (C.parameter_Icc_subset_source hrs ht)]
    _ = (AffineMap.lineMap p (p + d)) '' segment ℝ (0 : ℝ) r := by
      rw [segment_eq_Icc hr]
      congr 1
      funext t
      simp [AffineMap.lineMap_apply, add_comm]
    _ = _ := by
      rw [image_segment]
      simp [AffineMap.lineMap_apply, add_comm]

end Poincare.Topology.Plane.Curves.TransverseCutCoordinates

namespace Poincare.Topology.Plane.Curves.TransverseGraphCuts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
  (P : TransverseGraphCuts lo a b ua wa ub wb)


noncomputable def linearCoordinates (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    OpenPartialHomeomorph (ℝ × ℝ) E :=
  (P.coordinates hX hlo).trans L.toHomeomorph.toOpenPartialHomeomorph

theorem linearCoordinates_apply (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) (q : ℝ × ℝ) :
    P.linearCoordinates L hX hlo q = L (P.coordinates hX hlo q) := rfl

theorem smooth_linearCoordinates (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    ContDiffOn ℝ ∞ (P.linearCoordinates L hX hlo) (P.linearCoordinates L hX hlo).source :=
  L.contDiff.comp_contDiffOn ((P.smooth_coordinates hX hlo).mono (fun _ hq => hq.1))

theorem linearCoordinates_axis (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) (t : ℝ) :
    P.linearCoordinates L hX hlo (t, 0) = L (a + t * (b - a), lo (a + t * (b - a))) := by
  rw [P.linearCoordinates_apply, P.coordinates_apply, obliqueStripMap_bottom P.A_zero P.B_zero]

theorem linearCoordinates_axis_mem_source (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (hab : a < b) (hI : Icc a b ⊆ X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t, 0) ∈ (P.linearCoordinates L hX hlo).source := by
  refine ⟨?_, mem_univ _⟩
  change (t, 0) ∈ (P.coordinates hX hlo).source
  rw [coordinates, obliqueStripCoordinates_source]
  refine ⟨⟨by linarith [P.radius_pos], P.radius_pos⟩, ?_⟩
  rw [P.A_zero, P.B_zero]
  apply hI
  constructor <;> nlinarith [ht.1, ht.2]



theorem linearCoordinates_axis_fderiv (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (hab : a < b) (hI : Icc a b ⊆ X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fderiv ℝ (P.linearCoordinates L hX hlo) (t, 0) (1, 0) =
      (b - a) • L (1, deriv lo (a + t * (b - a))) := by
  let H := P.linearCoordinates L hX hlo
  have hsource := P.linearCoordinates_axis_mem_source L hX hlo hab hI ht
  have hdiff := (((P.smooth_linearCoordinates L hX hlo) _ hsource).contDiffAt
    (H.open_source.mem_nhds hsource)).differentiableAt (by simp)
  have harg : HasDerivAt (fun s : ℝ => a + s * (b - a)) (b - a) t := by
    simpa using ((hasDerivAt_id t).mul_const (b - a)).const_add a
  have hx : a + t * (b - a) ∈ X := by
    apply hI
    constructor <;> nlinarith [ht.1, ht.2]
  have hlo' := (((hlo _ hx).contDiffAt (hX.mem_nhds hx)).differentiableAt
    (by simp)).hasDerivAt
  have hgraph := L.hasFDerivAt.comp_hasDerivAt t (harg.prodMk (hlo'.comp t harg))
  have htrace : HasDerivAt (fun s : ℝ => H (s, 0))
      (L (b - a, deriv lo (a + t * (b - a)) * (b - a))) t := by
    have heq : (fun s : ℝ => H (s, 0)) =
        fun s => L (a + s * (b - a), lo (a + s * (b - a))) :=
      funext (P.linearCoordinates_axis L hX hlo)
    rw [heq]
    exact hgraph
  have hpath : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ))
  have hdpath : HasDerivAt (fun s : ℝ => H (s, 0)) (fderiv ℝ H (t, 0) (1, 0)) t :=
    hdiff.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, (0 : ℝ))) t hpath
  rw [← htrace.unique hdpath]
  have he : (b - a, deriv lo (a + t * (b - a)) * (b - a)) =
      (b - a) • ((1 : ℝ), deriv lo (a + t * (b - a))) := by
    ext <;> simp [smul_eq_mul, mul_comm]
  rw [he, map_smul]

theorem linearCoordinates_left (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {z : ℝ} (hz : z ∈ Ioo (-P.radius) P.radius) :
    P.linearCoordinates L hX hlo (0, z) = L (a, lo a) +
      P.left.parameter.symm z • L (ua, wa) := by
  rw [P.linearCoordinates_apply, P.coordinates_apply, obliqueStripMap_left, P.left_line_identity hz]
  have he : (a + P.left.parameter.symm z * ua, lo a + P.left.parameter.symm z * wa) =
      (a, lo a) + P.left.parameter.symm z • (ua, wa) := by ext <;> simp [smul_eq_mul]
  rw [he, map_add, map_smul]

theorem linearCoordinates_right (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {z : ℝ} (hz : z ∈ Ioo (-P.radius) P.radius) :
    P.linearCoordinates L hX hlo (1, z) = L (b, lo b) +
      P.right.parameter.symm z • L (ub, wb) := by
  rw [P.linearCoordinates_apply, P.coordinates_apply, obliqueStripMap_right, P.right_line_identity hz]
  have he : (b + P.right.parameter.symm z * ub, lo b + P.right.parameter.symm z * wb) =
      (b, lo b) + P.right.parameter.symm z • (ub, wb) := by ext <;> simp [smul_eq_mul]
  rw [he, map_add, map_smul]

theorem linearCoordinates_left_image (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {r : ℝ} (hr : 0 ≤ r) (hrs : r ∈ P.left.parameter.source)
    (hheight : P.left.parameter r < P.radius) :
    (fun z => P.linearCoordinates L hX hlo (0, z)) '' Icc (0 : ℝ) (P.left.parameter r) =
      segment ℝ (L (a, lo a)) (L (a, lo a) + r • L (ua, wa)) := by
  rw [← P.left.inverse_ray_image_Icc _ _ hr hrs]
  apply image_congr
  intro z hz
  exact P.linearCoordinates_left L hX hlo
    ⟨by linarith [P.radius_pos, hz.1], hz.2.trans_lt hheight⟩

theorem linearCoordinates_right_image (L : (ℝ × ℝ) ≃L[ℝ] E)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {r : ℝ} (hr : 0 ≤ r) (hrs : r ∈ P.right.parameter.source)
    (hheight : P.right.parameter r < P.radius) :
    (fun z => P.linearCoordinates L hX hlo (1, z)) '' Icc (0 : ℝ) (P.right.parameter r) =
      segment ℝ (L (b, lo b)) (L (b, lo b) + r • L (ub, wb)) := by
  rw [← P.right.inverse_ray_image_Icc _ _ hr hrs]
  apply image_congr
  intro z hz
  exact P.linearCoordinates_right L hX hlo
    ⟨by linarith [P.radius_pos, hz.1], hz.2.trans_lt hheight⟩

end Poincare.Topology.Plane.Curves.TransverseGraphCuts

namespace Poincare.Topology.Plane.Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem exists_adjacent_linear_oblique_width
    {lo₁ lo₂ : ℝ → ℝ} {a₁ b₁ ua₁ wa₁ ub₁ wb₁ a₂ b₂ ua₂ wa₂ ub₂ wb₂ : ℝ}
    (P : TransverseGraphCuts lo₁ a₁ b₁ ua₁ wa₁ ub₁ wb₁)
    (Q : TransverseGraphCuts lo₂ a₂ b₂ ua₂ wa₂ ub₂ wb₂)
    (L₁ L₂ : (ℝ × ℝ) ≃L[ℝ] E)
    {X₁ X₂ : Set ℝ} (hX₁ : IsOpen X₁) (hlo₁ : ContDiffOn ℝ ∞ lo₁ X₁)
    (hX₂ : IsOpen X₂) (hlo₂ : ContDiffOn ℝ ∞ lo₂ X₂)
    (hab₁ : a₁ < b₁) (hI₁ : Icc a₁ b₁ ⊆ X₁) (hab₂ : a₂ < b₂) (hI₂ : Icc a₂ b₂ ⊆ X₂)
    (hcommon : L₁ (b₁, lo₁ b₁) = L₂ (a₂, lo₂ a₂))
    (hcut : L₁ (ub₁, wb₁) = L₂ (ua₂, wa₂))
    (hbase : ∀ x ∈ Icc a₁ b₁, ∀ y ∈ Icc a₂ b₂,
      L₁ (x, lo₁ x) = L₂ (y, lo₂ y) → x = b₁ ∧ y = a₂)
    (ℓ : E →L[ℝ] ℝ) (hcutzero : ℓ (L₁ (ub₁, wb₁)) = 0)
    (htangent₁ : 0 < ℓ (L₁ (1, deriv lo₁ b₁)))
    (htangent₂ : 0 < ℓ (L₂ (1, deriv lo₂ a₂))) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (t, z) ∈ (P.linearCoordinates L₁ hX₁ hlo₁).source ∧
        (s, w) ∈ (Q.linearCoordinates L₂ hX₂ hlo₂).source ∧
        (P.linearCoordinates L₁ hX₁ hlo₁ (t, z) = Q.linearCoordinates L₂ hX₂ hlo₂ (s, w) →
          t = 1 ∧ s = 0) := by
  let F := P.linearCoordinates L₁ hX₁ hlo₁
  let G := Q.linearCoordinates L₂ hX₂ hlo₂
  have hFend : F (1, 0) = L₁ (b₁, lo₁ b₁) := by
    rw [P.linearCoordinates_axis]
    simp
  have hGend : G (0, 0) = L₂ (a₂, lo₂ a₂) := by
    rw [Q.linearCoordinates_axis]
    simp
  apply exists_adjacent_strip_separation F G
    ((P.smooth_linearCoordinates L₁ hX₁ hlo₁).of_le (by simp))
    ((Q.smooth_linearCoordinates L₂ hX₂ hlo₂).of_le (by simp))
    (fun _ ht => P.linearCoordinates_axis_mem_source L₁ hX₁ hlo₁ hab₁ hI₁ ht)
    (fun _ ht => Q.linearCoordinates_axis_mem_source L₂ hX₂ hlo₂ hab₂ hI₂ ht)
    (hFend.trans (hcommon.trans hGend.symm)) ?_ ℓ ?_ ?_ ?_ ?_
  · intro t ht s hs heq
    have hx : a₁ + t * (b₁ - a₁) ∈ Icc a₁ b₁ := by constructor <;> nlinarith [ht.1, ht.2]
    have hy : a₂ + s * (b₂ - a₂) ∈ Icc a₂ b₂ := by constructor <;> nlinarith [hs.1, hs.2]
    rw [P.linearCoordinates_axis, Q.linearCoordinates_axis] at heq
    have habs := hbase _ hx _ hy heq
    constructor <;> nlinarith [habs.1, habs.2]
  · rw [P.linearCoordinates_axis_fderiv L₁ hX₁ hlo₁ hab₁ hI₁ (by simp)]
    simpa using mul_pos (sub_pos.mpr hab₁) htangent₁
  · rw [Q.linearCoordinates_axis_fderiv L₂ hX₂ hlo₂ hab₂ hI₂ (by simp)]
    simpa using mul_pos (sub_pos.mpr hab₂) htangent₂
  · filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-P.radius) P.radius from
      ⟨by linarith [P.radius_pos], P.radius_pos⟩)] with z hz
    rw [P.linearCoordinates_right L₁ hX₁ hlo₁ hz, hFend]
    simp [hcutzero]
  · filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-Q.radius) Q.radius from
      ⟨by linarith [Q.radius_pos], Q.radius_pos⟩)] with z hz
    rw [Q.linearCoordinates_left L₂ hX₂ hlo₂ hz, hGend]
    simp [← hcut, hcutzero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem image_subgraph_slice (F : ℝ × ℝ → E) (h : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F '' ({q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
      {q | q.1 = t}) = (fun z => F (t, z)) '' Icc (0 : ℝ) (h t) := by
  ext p
  constructor
  · rintro ⟨⟨s, z⟩, ⟨⟨hs, hz⟩, hst⟩, rfl⟩
    dsimp at hst hz
    subst s
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(t, z), ⟨⟨ht, hz⟩, rfl⟩, rfl⟩




theorem exists_adjacent_linear_oblique_intersection
    {lo₁ lo₂ : ℝ → ℝ} {a₁ b₁ ua₁ wa₁ ub₁ wb₁ a₂ b₂ ua₂ wa₂ ub₂ wb₂ : ℝ}
    (P : TransverseGraphCuts lo₁ a₁ b₁ ua₁ wa₁ ub₁ wb₁)
    (Q : TransverseGraphCuts lo₂ a₂ b₂ ua₂ wa₂ ub₂ wb₂)
    (L₁ L₂ : (ℝ × ℝ) ≃L[ℝ] E)
    {X₁ X₂ : Set ℝ} (hX₁ : IsOpen X₁) (hlo₁ : ContDiffOn ℝ ∞ lo₁ X₁)
    (hX₂ : IsOpen X₂) (hlo₂ : ContDiffOn ℝ ∞ lo₂ X₂)
    (hab₁ : a₁ < b₁) (hI₁ : Icc a₁ b₁ ⊆ X₁) (hab₂ : a₂ < b₂) (hI₂ : Icc a₂ b₂ ⊆ X₂)
    (hcommon : L₁ (b₁, lo₁ b₁) = L₂ (a₂, lo₂ a₂))
    (hcut : L₁ (ub₁, wb₁) = L₂ (ua₂, wa₂))
    (hbase : ∀ x ∈ Icc a₁ b₁, ∀ y ∈ Icc a₂ b₂,
      L₁ (x, lo₁ x) = L₂ (y, lo₂ y) → x = b₁ ∧ y = a₂)
    (ℓ : E →L[ℝ] ℝ) (hcutzero : ℓ (L₁ (ub₁, wb₁)) = 0)
    (htangent₁ : 0 < ℓ (L₁ (1, deriv lo₁ b₁)))
    (htangent₂ : 0 < ℓ (L₂ (1, deriv lo₂ a₂))) :
    ∃ δ > 0, δ ≤ P.radius ∧ δ ≤ Q.radius ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ z w : ℝ, |z| < δ → |w| < δ →
          (t, z) ∈ (P.linearCoordinates L₁ hX₁ hlo₁).source ∧
          (s, w) ∈ (Q.linearCoordinates L₂ hX₂ hlo₂).source ∧
          (P.linearCoordinates L₁ hX₁ hlo₁ (t, z) = Q.linearCoordinates L₂ hX₂ hlo₂ (s, w) →
            t = 1 ∧ s = 0)) ∧
      ∀ h k : ℝ → ℝ,
        (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ h t ∧ h t < δ) →
        (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ k t ∧ k t < δ) →
        ∀ r : ℝ, 0 ≤ r → r ∈ P.right.parameter.source → r ∈ Q.left.parameter.source →
          h 1 = P.right.parameter r → k 0 = Q.left.parameter r →
          (P.linearCoordinates L₁ hX₁ hlo₁) ''
              {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
            (Q.linearCoordinates L₂ hX₂ hlo₂) ''
              {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ k q.1} =
            segment ℝ (L₁ (b₁, lo₁ b₁)) (L₁ (b₁, lo₁ b₁) + r • L₁ (ub₁, wb₁)) := by
  obtain ⟨ε, hε, hsep⟩ := exists_adjacent_linear_oblique_width P Q L₁ L₂ hX₁ hlo₁ hX₂ hlo₂
    hab₁ hI₁ hab₂ hI₂ hcommon hcut hbase ℓ hcutzero htangent₁ htangent₂
  let δ := min ε (min P.radius Q.radius)
  have hδ : 0 < δ := lt_min hε (lt_min P.radius_pos Q.radius_pos)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδP : δ ≤ P.radius := (min_le_right _ _).trans (min_le_left _ _)
  have hδQ : δ ≤ Q.radius := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδP, hδQ, ?_, ?_⟩
  · intro t ht s hs z w hz hw
    exact hsep t ht s hs z w (hz.trans_le hδε) (hw.trans_le hδε)
  · intro h k hh hk r hr hrP hrQ hhend hkend
    apply image_inter_eq_of_endpoint_separation
    · intro q hq v hv heq
      have hqheight : |q.2| < ε := by
        rw [abs_of_nonneg hq.2.1]
        exact (hq.2.2.trans_lt (hh q.1 hq.1).2).trans_le hδε
      have hvheight : |v.2| < ε := by
        rw [abs_of_nonneg hv.2.1]
        exact (hv.2.2.trans_lt (hk v.1 hv.1).2).trans_le hδε
      exact (hsep q.1 hq.1 v.1 hv.1 q.2 v.2 hqheight hvheight).2.2 heq
    · rw [image_subgraph_slice _ h (by simp), hhend]
      exact P.linearCoordinates_right_image L₁ hX₁ hlo₁ hr hrP
        (hhend ▸ ((hh 1 (by simp)).2.trans_le hδP))
    · rw [image_subgraph_slice _ k (by simp), hkend]
      rw [Q.linearCoordinates_left_image L₂ hX₂ hlo₂ hr hrQ
        (hkend ▸ ((hk 0 (by simp)).2.trans_le hδQ))]
      rw [hcommon, hcut]

end Poincare.Topology.Plane.Curves
