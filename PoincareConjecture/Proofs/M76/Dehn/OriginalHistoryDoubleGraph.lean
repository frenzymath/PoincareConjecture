import PoincareConjecture.Proofs.M76.Dehn.OriginalHistoryAffineCover
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleSourcePolyhedron
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds











set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}






theorem Step.exists_finite_history_double_graph
    {s t : Stage e S f r C} (step : Step s t)
    {K : SimplicialComplex ℝ V2} (hK : K.faces.Finite)
    (A : SimplicialComplex ℝ V2) (hA : A.space = Metric.sphere (0 : V2) 1)
    {n : ℕ} (order : Fin n → K.faces) (horder : Function.Bijective order)
    (hbefore : ∀ i k, (order k).val ⊂ (order i).val → k < i)
    (hphase : ∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces)
    (P : ℕ → SimplicialComplex ℝ V2)
    (hP : ∀ k, P k ≤ K ∧
      (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a})
    (hsucc : ∀ i : Fin n, (P (i.val + 1)).space = (P i.val).space ∪
      convexHull ℝ ((order i).val : Set V2))
    (boundary : Fin n → Bool)
    (hboundary : ∀ i, boundary i = true ↔ (order i).val ∈ A.faces)
    (Q : Fin n → OpenPartialHomeomorph t.Carrier V3)
    (B : Fin n → OpenPartialHomeomorph s.Carrier V3)
    (J : Fin n → SimplicialComplex ℝ V3)
    (hQ : ∀ i k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid V3)
    (hB : ∀ i k, (s.charts k).symm.trans (B i) ∈ piecewiseAffineGroupoid V3)
    (hval : ∀ i z, Q i z = B i (step.projection (step.inclusion z)))
    (hmaps : ∀ i, MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source)
    (U : K.faces → Set t.Carrier) (hUQ : ∀ i, U (order i) ⊆ (Q i).source)
    {R Fmark : Set M} (states : ℕ → FaceDiskState t K U R Fmark)
    (motions : ∀ i : Fin n,
      FaceMotionData step K (P i.val) (P (i.val + 1)) (states i.val).map
        (Q i) (B i) (J i) U R Fmark (boundary i))
    (htransitions : ∀ i : Fin n,
      (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map)
    (hstable : ∀ i k, i ≤ k → k ≤ n →
      EqOn (states k).map (states i).map (P i).space)
    (hcell : ∀ a : K.faces, InjOn ((step.projection ∘ step.inclusion) ∘ (states n).map)
      (convexHull ℝ (a.val : Set V2))) :
    ∃ (L : SimplicialComplex ℝ (V2 × V2)) (G : SimplicialComplex ℝ V2)
      (H : L.space ≃ₜ G.space),
      L.faces.Finite ∧ G.faces.Finite ∧
      L.space = {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
        step.projection (step.inclusion ((states n).map z.1)) =
          step.projection (step.inclusion ((states n).map z.2)) ∧ z.1 ≠ z.2} ∧
      G.space = {x | x ∈ K.space ∧ ∃ y ∈ K.space, x ≠ y ∧
        step.projection (step.inclusion ((states n).map x)) =
          step.projection (step.inclusion ((states n).map y))} ∧
      (∀ a ∈ L.faces, a.card ≤ 2) ∧ (∀ a ∈ G.faces, a.card ≤ 2) ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧ ∀ z : L.space, (H z : V2) = z.val.1 := by
  obtain ⟨T, hT, hcover⟩ := step.exists_finite_history_affine_cover hK A hA
    order horder hbefore hphase P hP hsucc boundary hboundary Q B J hQ hB hval hmaps
    U hUQ states motions htransitions hstable hcell
  obtain ⟨L, G, H, hL, hG, hLs, hGs, hH, hHi, hHval⟩ :=
    step.exists_finite_double_source_polyhedron K hK (states n).original_PL (states n).embedding
  have hLcover : ∀ z ∈ L.space, ∃ A' ∈ T, z ∈ A' := by
    intro z hz
    have h := hLs.subset hz
    exact hcover z h.1 h.2.1 h.2.2.2 h.2.2.1
  have hLcard : ∀ a ∈ L.faces, a.card ≤ 2 :=
    fun a ha => L.face_card_le_of_finite_affine_cover T hT hLcover ha
  let first : V2 × V2 →ᴬ[ℝ] V2 := (ContinuousLinearMap.fst ℝ V2 V2).toContinuousAffineMap
  have hfirst := (L.affineOnFaces_affine first).finitePiecewiseAffineOn hL
  obtain ⟨T', hT', hcover'⟩ :=
    hfirst.exists_finite_affine_image_cover (C := L.space) Subset.rfl T hT hLcover
  have hGcover : ∀ x ∈ G.space, ∃ A' ∈ T', x ∈ A' := by
    intro x hx
    obtain ⟨hxK, y, hyK, hne, hxy⟩ := hGs.subset hx
    exact hcover' x ⟨(x, y), hLs.symm.subset ⟨hxK, hyK, hxy, hne⟩, rfl⟩
  have hGcard : ∀ a ∈ G.faces, a.card ≤ 2 :=
    fun a ha => G.face_card_le_of_finite_affine_cover T' hT' hGcover ha
  exact ⟨L, G, H, hL, hG, hLs, hGs, hLcard, hGcard, hH, hHi, hHval⟩

end Geometry.OriginalPLTower
