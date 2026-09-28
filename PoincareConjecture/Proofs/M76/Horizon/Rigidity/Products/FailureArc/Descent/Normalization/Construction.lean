import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FiniteHistory
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteMarkedFacePrefixes

set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_marked_surface_normalization_history
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (K₀ A₀ : SimplicialComplex ℝ V) (hK₀ : K₀.faces.Finite) (hA₀ : A₀.faces.Finite)
    (hA₀K₀ : A₀.space ⊆ K₀.space)
    (he : PoincareConjecture.M76.PLDomain e R)
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K₀.space)
    (hji : IsEmbedding (fun x : K₀.space => j x))
    (hjR : MapsTo j K₀.space (t.projection ⁻¹' R))
    (hproper : ∀ x : K₀.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ (x : V) ∈ A₀.space)
    (hjF : ∀ x : A₀.space, t.projection (j x) ∈ Fmark) :
    ∃ (W : Set M) (K A : SimplicialComplex ℝ V),
      IsOpen W ∧ Fmark = frontier R ∩ W ∧
      K.faces.Finite ∧ K.space = K₀.space ∧ A.faces.Finite ∧ A ≤ K ∧ A.space = A₀.space ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ A.vertices) → a ∈ A.faces) ∧
      ∃ (n : ℕ) (order : Fin n → K.faces),
        Function.Bijective order ∧
        (∀ i k, (order k).val ⊂ (order i).val → k < i) ∧
        (∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces) ∧
        ∃ P : ℕ → SimplicialComplex ℝ V,
          (∀ k, (P k).faces.Finite ∧ P k ≤ K ∧
            (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a}) ∧
          (P 0).space = ∅ ∧ (P n).space = K.space ∧ Monotone P ∧
          ∃ (boundary : Fin n → Bool)
            (Q : Fin n → OpenPartialHomeomorph t.Carrier V3)
            (B : Fin n → OpenPartialHomeomorph s.Carrier V3)
            (J : Fin n → SimplicialComplex ℝ V3) (U : K.faces → Set t.Carrier),
            (∀ i, boundary i = true ↔ (order i).val ∈ A.faces) ∧
            (∀ i : Fin n,
              (P (i.val + 1)).space = (P i.val).space ∪
                convexHull ℝ ((order i).val : Set V)) ∧
            (∀ i : Fin n,
              (boundary i = true → (P (i.val + 1)).space ⊆ A₀.space) ∧
              (boundary i = false → A₀.space ⊆ (P i.val).space)) ∧
            (∀ i, InjOn (step.projection ∘ step.inclusion) (Q i).source ∧
              (∀ k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid V3) ∧
              (∀ k, (s.charts k).symm.trans (B i) ∈ piecewiseAffineGroupoid V3) ∧
              (Q i).target = (B i).target ∧
              (∀ y, Q i y = B i (step.projection (step.inclusion y))) ∧
              MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source ∧
              EqOn ((step.projection ∘ step.inclusion) ∘ (Q i).symm)
                (B i).symm (B i).target ∧
              (J i).faces.Finite ∧ Convex ℝ (J i).space ∧ (J i).space ⊆ (Q i).target ∧
              (boundary i = true → (Q i).source ⊆ t.projection ⁻¹' W) ∧
              ((B i).source ⊆ interior (s.projection ⁻¹' R) ∨
                ∃ ell : V3 →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
                  (∀ y ∈ (B i).source,
                    y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B i y)) ∧
                  ∀ y ∈ (B i).source,
                    y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B i y) = 0)) ∧
            (∀ a, IsOpen (U a)) ∧
            (∀ i, U (order i) ⊆ (Q i).source ∩ (Q i) ⁻¹' interior (J i).space) ∧
            ∃ states : ℕ → MarkedSurfaceState t K U R Fmark A₀.space,
              (states 0).map = j ∧
              (∀ i (hi : i < n),
                ∃ motion : MarkedSurfaceMotionData step K (P i) (P (i + 1)) (states i).map
                  (Q ⟨i, hi⟩) (B ⟨i, hi⟩) (J ⟨i, hi⟩) U R Fmark (boundary ⟨i, hi⟩),
                  (states (i + 1)).map = motion.ambient 1 ∘ (states i).map) ∧
              (∀ i k, i ≤ k → k ≤ n →
                EqOn (states k).map (states i).map (P i).space) ∧
              ∀ a : K.faces, InjOn ((step.projection ∘ step.inclusion) ∘ (states n).map)
                (convexHull ℝ (a.val : Set V)) := by
  classical
  obtain ⟨W, K, A, hW, hFW, hK, hKs, hA, hAK, hAs, hfull, hcharts⟩ :=
    step.exists_marked_surface_face_charts K₀ A₀ hK₀ hA₀ hA₀K₀ he hF hopen hj hji hjR hproper hjF
  choose center Q B radius J hxQ hinj hQ hB htarget hval hmaps hinv ha hJ hJs hJQ
    hsmall hlarge hmark hmodel hface _ using fun a : K.faces => hcharts a a.property
  let U (a : K.faces) : Set t.Carrier :=
    (Q a).source ∩ (Q a) ⁻¹' ball (Q a (j (center a))) (2 * radius a)
  have hU (a : K.faces) : IsOpen (U a) := (Q a).isOpen_inter_preimage isOpen_ball
  have hUbox (a : K.faces) : U a ⊆ (Q a).source ∩ (Q a) ⁻¹' interior (J a).space :=
    fun _ hx => ⟨hx.1, hlarge a (subset_closure hx.2)⟩
  have hretain (a : K.faces) : MapsTo j (convexHull ℝ (a.val : Set V)) (U a) :=
    fun x hx => ⟨(hface a x hx).1, hsmall a (subset_closure (hface a x hx).2)⟩
  have hcv (a : K.faces) : Convex ℝ (J a).space := by
    rw [hJs a]
    exact convex_closedBall _ _
  have hmodel' (a : K.faces) : (B a).source ⊆ interior (s.projection ⁻¹' R) ∨
      ∃ ell : V3 →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
        (∀ y ∈ (B a).source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B a y)) ∧
        ∀ y ∈ (B a).source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B a y) = 0 := by
    rcases hmodel a with hinside | ⟨ell, v, hv, _, hhalf, hfront⟩
    · exact Or.inl hinside
    · refine Or.inr ⟨ell, ?_, hhalf, hfront⟩
      intro hell
      have hz : ell.contLinear v = 0 := by
        change ell.toAffineMap.linear v = 0
        rw [hell]
        rfl
      exact zero_ne_one (hz.symm.trans hv)
  obtain ⟨n, faces, hinjective, hrange, hbefore, hphase, _, _⟩ :=
    K.exists_marked_face_order A hK hAK
  have hfaces (i : Fin n) : faces i ∈ K.faces := hrange.subset ⟨i, rfl⟩
  let order (i : Fin n) : K.faces := ⟨faces i, hfaces i⟩
  have horder : Function.Bijective order := by
    constructor
    · intro i k hik
      exact hinjective (congrArg Subtype.val hik)
    · intro a
      obtain ⟨i, hi⟩ := hrange.symm.subset a.property
      exact ⟨i, Subtype.ext hi⟩
  obtain ⟨P, hP, hPzero, hPn, hPsucc⟩ :=
    K.exists_finite_marked_face_prefixes A hK hAK faces hrange hbefore hphase
  have hmon : Monotone P := by
    intro k l hkl a haP
    obtain ⟨i, hi, rfl⟩ := (hP k).2.2.1.subset haP
    exact (hP l).2.2.1.symm.subset ⟨i, hi.trans_le hkl, rfl⟩
  let boundary (i : Fin n) : Bool := decide (faces i ∈ A.faces)
  have hboundary (i : Fin n) : boundary i = true ↔ faces i ∈ A.faces := decide_eq_true_iff
  have hPboundary (i : Fin n) :
      (boundary i = true → (P (i.val + 1)).space ⊆ A₀.space) ∧
      (boundary i = false → A₀.space ⊆ (P i.val).space) := by
    constructor
    · intro hi
      have hiA := (hboundary i).mp hi
      rw [(hPsucc i).1]
      exact union_subset
        ((SimplicialComplex.space_subset_of_le ((hPsucc i).2.1 hiA)).trans hAs.subset)
        ((A.convexHull_subset_space hiA).trans hAs.subset)
    · intro hi
      have hiA : faces i ∉ A.faces := of_decide_eq_false hi
      exact hAs.symm.subset.trans (SimplicialComplex.space_subset_of_le ((hPsucc i).2.2 hiA))
  let initial : MarkedSurfaceState t K U R Fmark A₀.space :=
    { map := j
      original_PL := by rw [hKs]; exact hj
      embedding := hji.comp (IsEmbedding.inclusion hKs.subset)
      region := fun _ hx => hjR (hKs.subset hx)
      proper := fun x hx => hproper ⟨x, hKs.subset hx⟩
      mark := fun x hx => hjF ⟨x, hx⟩
      retained := hretain }
  obtain ⟨states, hstates0, hsteps, hstable⟩ :=
    step.exists_marked_surface_face_history K hK faces hfaces P hmon (fun k _ => (hP k).2.1)
      (fun i => (hPsucc i).1) boundary A₀.space hPboundary hFW
      (fun i => Q (order i)) (fun i => B (order i)) (fun i => J (order i))
      (fun i => hQ (order i)) (fun i => hB (order i)) (fun i => htarget (order i))
      (fun i => hval (order i)) (fun i => hmaps (order i))
      (fun i hi => hmark (order i) ((hboundary i).mp hi))
      (fun i => hJ (order i)) (fun i => hcv (order i)) (fun i => hJQ (order i))
      (fun i => hmodel' (order i)) U hU (fun i => hUbox (order i)) initial
  refine ⟨W, K, A, hW, hFW, hK, hKs, hA, hAK, hAs, hfull,
    n, order, horder, hbefore, hphase, P,
    fun k => ⟨(hP k).1, (hP k).2.1, (hP k).2.2.1⟩,
    hPzero, hPn, hmon, boundary,
    (fun i => Q (order i)), (fun i => B (order i)), (fun i => J (order i)), U,
    hboundary, (fun i => (hPsucc i).1), hPboundary, ?_, hU,
    (fun i => hUbox (order i)), states, ?_, hsteps, hstable, ?_⟩
  · intro i
    exact ⟨hinj (order i), hQ (order i), hB (order i), htarget (order i), hval (order i),
      hmaps (order i), hinv (order i), hJ (order i), hcv (order i), hJQ (order i),
      (fun hi => hmark (order i) ((hboundary i).mp hi)), hmodel' (order i)⟩
  · rw [hstates0]
  · intro a x hx y hy hxy
    have hxQ := ((states n).retained a hx).1
    have hyQ := ((states n).retained a hy).1
    have hmap : (states n).map x = (states n).map y := hinj a hxQ hyQ hxy
    have hsub : (⟨x, K.convexHull_subset_space a.property hx⟩ : K.space) =
        ⟨y, K.convexHull_subset_space a.property hy⟩ := (states n).embedding.injective hmap
    exact congrArg Subtype.val hsub

end Geometry.OriginalPLTower
