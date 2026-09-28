import PoincareConjecture.Proofs.M76.Dehn.OriginalDiskFaceHistory
import PoincareConjecture.Proofs.M76.Dehn.OriginalFaceHistoryHomotopy

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Qrim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_original_marked_face_assembly
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R)
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j D)
    (hji : IsEmbedding (fun x : D => j x))
    (hjR : MapsTo j D (t.projection ⁻¹' R))
    (hproper : ∀ x : D, j x ∈ frontier (t.projection ⁻¹' R) ↔ (x : V2) ∈ Qrim)
    (rim : C(Qrim, Fmark))
    (hrim : ∀ x : Qrim, t.projection (j x) = (rim x : M))
    {base : Fmark} (q : Path base (rim squareRimBase))
    (Jgroup : Subgroup (FundamentalGroup Fmark base))
    (hout : q.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ Jgroup) :
    ∃ (W : Set M) (K A : SimplicialComplex ℝ V2),
      IsOpen W ∧ Fmark = frontier R ∩ W ∧
      K.faces.Finite ∧ K.space = D ∧ A.faces.Finite ∧ A ≤ K ∧ A.space = Qrim ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ A.vertices) → a ∈ A.faces) ∧
      ∃ (n : ℕ) (order : Fin n → K.faces),
        Function.Bijective order ∧
        (∀ i k, (order k).val ⊂ (order i).val → k < i) ∧
        (∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces) ∧
        ∃ P : ℕ → SimplicialComplex ℝ V2,
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
                convexHull ℝ ((order i).val : Set V2)) ∧
            (∀ i : Fin n,
              (boundary i = true → (P (i.val + 1)).space ⊆ Qrim) ∧
              (boundary i = false → Qrim ⊆ (P i.val).space)) ∧
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
            ∃ states : ℕ → FaceDiskState t K U R Fmark,
              (states 0).map = j ∧
              (∀ i (hi : i < n),
                ∃ motion : FaceMotionData step K (P i) (P (i + 1)) (states i).map
                  (Q ⟨i, hi⟩) (B ⟨i, hi⟩) (J ⟨i, hi⟩) U R Fmark (boundary ⟨i, hi⟩),
                  (states (i + 1)).map = motion.ambient 1 ∘ (states i).map) ∧
              (∀ i k, i ≤ k → k ≤ n →
                EqOn (states k).map (states i).map (P i).space) ∧
              (∀ a : K.faces,
                InjOn ((step.projection ∘ step.inclusion) ∘ (states n).map)
                  (convexHull ℝ (a.val : Set V2))) ∧
              ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (rim' : C(Qrim, Fmark))
                (eta : rim.Homotopy rim'),
                Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
                Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
                (∀ x, G 0 x = x) ∧
                (∀ a, (G a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
                  (G a) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
                (states n).map = G 1 ∘ j ∧
                (∀ a x, (eta (a, x) : M) = t.projection (G a (j x))) ∧
                (∀ x : Qrim, t.projection ((states n).map x) = (rim' x : M)) ∧
                (q.trans (eta.evalAt squareRimBase)).whiskeredLoopClass
                  (squareRimLoop.map rim'.continuous) ∉ Jgroup := by
  have hjF (x : Qrim) : t.projection (j x) ∈ Fmark := by
    rw [hrim x]
    exact (rim x).property
  obtain ⟨W, K, A, hW, hFW, hK, hKs, hA, hAK, hAs, hfull,
    n, order, horder, hbefore, hphase, P, hP, hPzero, hPn, hmon,
    boundary, Q, B, J, U, hboundary, hPsucc, hPphase, hcharts, hU, hUbox,
    states, hstates0, hsteps, hstable, hface⟩ :=
    step.exists_original_disk_face_history he hF hopen hj hji hjR hproper hjF
  have hrim0 (x : Qrim) : t.projection ((states 0).map x) = (rim x : M) := by
    rw [hstates0, hrim x]
  obtain ⟨G, rim', eta, hG, hGi, hzero, hsets, hfinal, htrace, hrim', hout'⟩ :=
    step.exists_original_face_history_homotopy hKs states hsteps rim hrim0 q Jgroup hout
  refine ⟨W, K, A, hW, hFW, hK, hKs, hA, hAK, hAs, hfull,
    n, order, horder, hbefore, hphase, P, hP, hPzero, hPn, hmon,
    boundary, Q, B, J, U, hboundary, hPsucc, hPphase, hcharts, hU, hUbox,
    states, hstates0, hsteps, hstable, hface,
    G, rim', eta, hG, hGi, hzero, hsets, ?_, ?_, hrim', hout'⟩
  · rw [hstates0] at hfinal
    exact hfinal
  · intro a x
    rw [htrace a x, hstates0]

end Geometry.OriginalPLTower
