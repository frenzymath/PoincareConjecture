import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryDualIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Geometry AffineMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K L : SimplicialComplex ℝ E)
  [Fintype K.faces] [Finite L.faces]

theorem exists_boundary_facet_product (hLK : L ≤ K)
    {n : ℕ} (hKcard : ∀ u ∈ K.faces, u.card ≤ n + 1)
    (hLcard : ∀ u ∈ L.faces, u.card ≤ n)
    {s t : Finset E} (hs : s ∈ L.faces) (hscard : s.card = n)
    (ht : t ∈ K.faces) (htcard : t.card = n + 1) (hst : s ⊆ t)
    (hunique : ∀ u ∈ K.faces, u.card = n + 1 → s ⊆ u → u = t) :
    ∃ F : Icc (0 : ℝ) 1 ≃ₜ (K.barycentricDualBlock s).space,
      F.IsFinitePL ∧
      (∀ u, (F u : E) = lineMap (s.centroid ℝ id) (t.centroid ℝ id) (u : ℝ)) ∧
      ∀ u, (F u : E) ∈ L.space ↔ (u : ℝ) = 0 := by
  obtain ⟨hcarrier, hcontact, hne⟩ := K.barycentricDualBlock_boundary_interval
    L hLK hKcard hLcard hs hscard ht htcard hst hunique
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hI
  let f : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap (s.centroid ℝ id) (t.centroid ℝ id)
  have hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) :=
    ⟨J, hJ, hJs, J.affineOnFaces_affine f⟩
  have himage : f '' Icc (0 : ℝ) 1 = (K.barycentricDualBlock s).space := by
    rw [hcarrier]
    exact (segment_eq_image_lineMap ℝ _ _).symm
  have hex := hf.exists_homeomorph_image (lineMap_injective ℝ hne).injOn
  rw [himage] at hex
  obtain ⟨F, hF, hvalue⟩ := hex
  refine ⟨F, hF, hvalue, ?_⟩
  intro u
  constructor
  · intro hu
    have hz : (F u : E) = s.centroid ℝ id := hcontact.subset ⟨(F u).property, hu⟩
    have heq : lineMap (s.centroid ℝ id) (t.centroid ℝ id) (u : ℝ) =
        lineMap (s.centroid ℝ id) (t.centroid ℝ id) (0 : ℝ) := by
      change f (u : ℝ) = f 0
      rw [← hvalue]
      change (F u : E) = lineMap (s.centroid ℝ id) (t.centroid ℝ id) (0 : ℝ)
      rw [lineMap_apply_zero]
      exact hz
    exact lineMap_injective ℝ hne heq
  · intro hu
    have hz : (F u : E) = s.centroid ℝ id := by
      rw [hvalue]
      change lineMap (s.centroid ℝ id) (t.centroid ℝ id) (u : ℝ) = _
      rw [hu, lineMap_apply_zero]
    exact (hcontact.symm.subset hz).2

theorem exists_boundary_triangle_products (hLK : L ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hboundary : ∀ s ∈ L.faces, ∃ t ∈ L.faces, s ⊆ t ∧ t.card = 3)
    (hfacets : ∀ s ∈ L.faces, s.card = 3 →
      {t | t ∈ K.faces ∧ t.card = 4 ∧ s ⊆ t}.ncard = 1)
    {s : Finset E} (hs : s ∈ L.faces) (hscard : s.card = 3) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4 ∧
      ∃ F : Icc (0 : ℝ) 1 ≃ₜ (K.barycentricDualBlock s).space,
        F.IsFinitePL ∧
        (∀ u, (F u : E) = lineMap (s.centroid ℝ id) (t.centroid ℝ id) (u : ℝ)) ∧
        ∀ u, (F u : E) ∈ L.space ↔ (u : ℝ) = 0 := by
  obtain ⟨t, ht⟩ := ncard_eq_one.mp (hfacets s hs hscard)
  have htmem : t ∈ {u | u ∈ K.faces ∧ u.card = 4 ∧ s ⊆ u} :=
    ht.symm.subset (mem_singleton t)
  obtain ⟨F, hF⟩ := K.exists_boundary_facet_product L hLK
    (n := 3) (fun u hu => by
      obtain ⟨v, _, huv, hvcard⟩ := hpure u hu
      simpa [hvcard] using Finset.card_le_card huv)
    (fun u hu => by
      obtain ⟨v, _, huv, hvcard⟩ := hboundary u hu
      simpa [hvcard] using Finset.card_le_card huv)
    hs hscard htmem.1 htmem.2.1 htmem.2.2 (fun u hu hucard hsu =>
      ht.subset ⟨hu, hucard, hsu⟩)
  exact ⟨t, htmem.1, htmem.2.2, htmem.2.1, F, hF⟩

end Geometry.SimplicialComplex
