import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseArcCuts
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.EndpointBarriers













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture




theorem m64Intrinsic_graph_parameter_deriv_pos
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (G : OpenPartialHomeomorph ℝ ℝ)
    {f : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G G.source)
    (hf : ContDiffOn ℝ ∞ f G.target) (hmono : StrictMonoOn G G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    {t : ℝ} (ht : t ∈ G.source) (hregular : deriv gamma t ≠ 0) : 0 < deriv G t := by
  have htan := m64Intrinsic_graph_tangent hg L G hG hf hgraph ht
  have hnonneg : 0 ≤ deriv G t := by
    rw [← derivWithin_of_isOpen G.open_source ht]
    exact hmono.monotoneOn.derivWithin_nonneg
  have hne : deriv G t ≠ 0 := by
    intro hz
    apply hregular
    apply L.injective
    rw [htan, hz, zero_smul, map_zero]
  exact lt_of_le_of_ne hnonneg hne.symm




theorem m64Intrinsic_graph_separator_sign
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (G : OpenPartialHomeomorph ℝ ℝ)
    {f : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G G.source)
    (hf : ContDiffOn ℝ ∞ f G.target) (hmono : StrictMonoOn G G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    {t : ℝ} (ht : t ∈ G.source) (hregular : deriv gamma t ≠ 0)
    (ell : AnnulusCoordinates →L[ℝ] ℝ) (terminal : Bool)
    (hsign : if terminal then ell (deriv gamma t) < 0 else 0 < ell (deriv gamma t)) :
    if terminal then (ell.comp L.symm.toContinuousLinearMap) (1, deriv f (G t)) < 0
      else 0 < (ell.comp L.symm.toContinuousLinearMap) (1, deriv f (G t)) := by
  have hd := m64Intrinsic_graph_parameter_deriv_pos hg L G hG hf hmono hgraph ht hregular
  have htan := m64Intrinsic_graph_tangent hg L G hG hf hgraph ht
  have heq : ell (deriv gamma t) =
      deriv G t * (ell.comp L.symm.toContinuousLinearMap) (1, deriv f (G t)) := by
    simpa only [L.symm_apply_apply, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using congrArg (fun v => ell (L.symm v)) htan
  rw [heq] at hsign
  cases terminal
  · exact (mul_pos_iff_of_pos_left hd).mp hsign
  · exact neg_of_mul_neg_right hsign hd.le




theorem m64Intrinsic_exists_obstacle_avoiding_graph_strip
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (G : OpenPartialHomeomorph ℝ ℝ)
    {f : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G G.source)
    (hf : ContDiffOn ℝ ∞ f G.target) (hmono : StrictMonoOn G G.source)
    (hI : Icc a b ⊆ G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    (himage : G '' Icc a b = Icc (G a) (G b))
    {C : Set AnnulusCoordinates} (hC : IsClosed C)
    (havoid : ∀ t ∈ Ioo a b, gamma t ∉ C)
    (da db : AnnulusCoordinates)
    (P : TransverseGraphCuts f (G a) (G b) (L da).1 (L da).2 (L db).1 (L db).2)
    (ellA ellB : AnnulusCoordinates →L[ℝ] ℝ)
    (hcutA : ellA da = 0) (hcutB : ellB db = 0)
    (htangentA : 0 < ellA (deriv gamma a)) (htangentB : ellB (deriv gamma b) < 0)
    {WA WB : Set AnnulusCoordinates} (hWA : IsOpen WA) (hWB : IsOpen WB)
    (haW : gamma a ∈ WA) (hbW : gamma b ∈ WB)
    (hsepA : ∀ z ∈ C ∩ WA, ellA (z - gamma a) ≤ 0)
    (hsepB : ∀ z ∈ C ∩ WB, ellB (z - gamma b) ≤ 0) :
    ∃ delta > 0, delta ≤ P.radius ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < delta →
        (t, z) ∈ (P.linearCoordinates L.symm G.open_target hf).source) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < delta →
        P.linearCoordinates L.symm G.open_target hf (t, z) ∉ C := by
  have ha := hI (left_mem_Icc.mpr hab.le)
  have hb := hI (right_mem_Icc.mpr hab.le)
  have hGI : Icc (G a) (G b) ⊆ G.target := by
    rw [← himage]
    rintro _ ⟨t, ht, rfl⟩
    exact G.map_source (hI ht)
  have havoid' : ∀ x ∈ Ioo (G a) (G b), (x, f x) ∉ L '' C := by
    intro x hx hmem
    obtain ⟨t, ht, rfl⟩ := himage.symm ▸ Ioo_subset_Icc_self hx
    have hat : a < t := by
      by_contra hn
      have heq : t = a := le_antisymm (le_of_not_gt hn) ht.1
      exact (ne_of_lt hx.1) (congrArg G heq.symm)
    have htb : t < b := by
      by_contra hn
      have heq : t = b := le_antisymm ht.2 (le_of_not_gt hn)
      exact (ne_of_lt hx.2) (congrArg G heq)
    obtain ⟨u, hu, heq⟩ := hmem
    have htu : gamma t = u := L.injective ((hgraph t (hI ht)).trans heq.symm)
    exact havoid t ⟨hat, htb⟩ (htu.symm ▸ hu)
  let mA := ellA.comp L.symm.toContinuousLinearMap
  let mB := ellB.comp L.symm.toContinuousLinearMap
  have hka : mA ((L da).1, (L da).2) = 0 := by
    simpa only [mA, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Prod.eta, L.symm_apply_apply] using hcutA
  have hkb : mB ((L db).1, (L db).2) = 0 := by
    simpa only [mB, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Prod.eta, L.symm_apply_apply] using hcutB
  have hta : 0 < mA (1, deriv f (G a)) := m64Intrinsic_graph_separator_sign
    hg L G hG hf hmono hgraph ha (hregular a (left_mem_Icc.mpr hab.le)) ellA false htangentA
  have htb : mB (1, deriv f (G b)) < 0 := m64Intrinsic_graph_separator_sign
    hg L G hG hf hmono hgraph hb (hregular b (right_mem_Icc.mpr hab.le)) ellB true htangentB
  have hsa : ∀ q ∈ (L '' C) ∩ (L '' WA), mA (q - (G a, f (G a))) ≤ 0 := by
    rintro q ⟨⟨u, hu, rfl⟩, v, hv, hvu⟩
    have huW : u ∈ WA := L.injective hvu ▸ hv
    change ellA (L.symm (L u - (G a, f (G a)))) ≤ 0
    rw [← hgraph a ha, ← map_sub, L.symm_apply_apply]
    exact hsepA u ⟨hu, huW⟩
  have hsb : ∀ q ∈ (L '' C) ∩ (L '' WB), mB (q - (G b, f (G b))) ≤ 0 := by
    rintro q ⟨⟨u, hu, rfl⟩, v, hv, hvu⟩
    have huW : u ∈ WB := L.injective hvu ▸ hv
    change ellB (L.symm (L u - (G b, f (G b)))) ≤ 0
    rw [← hgraph b hb, ← map_sub, L.symm_apply_apply]
    exact hsepB u ⟨hu, huW⟩
  obtain ⟨delta, hdelta, hdeltaP, hsource, hseparate, _⟩ := P.exists_avoiding_strip
    G.open_target hf (hmono ha hb hab) hGI (L.toHomeomorph.isClosedMap C hC) havoid'
    mA mB hka hkb hta htb
    (L.toHomeomorph.isOpenMap WA hWA) (L.toHomeomorph.isOpenMap WB hWB)
    ⟨gamma a, haW, hgraph a ha⟩ ⟨gamma b, hbW, hgraph b hb⟩ hsa hsb
  refine ⟨delta, hdelta, hdeltaP, fun t ht z hz => ⟨hsource t ht z hz, mem_univ _⟩, ?_⟩
  intro t ht z hz hmem
  apply hseparate t ht z hz
  refine ⟨P.linearCoordinates L.symm G.open_target hf (t, z), hmem, ?_⟩
  rw [P.linearCoordinates_apply]
  exact L.apply_symm_apply _

end PoincareConjecture
