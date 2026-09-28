import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ArcEndpointCapModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.CappedPairedCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PairedChartRestriction
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_endpoint_capped_scene
    (P : Fin 3 → SimplicialComplex ℝ V3) (hP : ∀ i, (P i).faces.Finite)
    (A : Set V3) (p : Fin 2 → V3) (hPa : (P 2).space = A)
    (hd : IsFinitePLBallPair ℝ A {p 0, p 1}) (hpne : p 0 ≠ p 1)
    (W : Set V3) (hW : IsOpen W) (hAW : A ⊆ W)
    (hisolate : ∀ x ∈ W, x ∈ A ↔ x ∈ (P 0).space ∧ x ∈ (P 1).space)
    (B : Fin 2 → OpenPartialHomeomorph V3 V3)
    (hB : ∀ i, B i ∈ piecewiseAffineGroupoid V3)
    (hpB : ∀ i, p i ∈ (B i).source) (hBp : ∀ i, B i (p i) = 0)
    (htriangle : ∀ i x, x ∈ (B i).source →
      (x ∈ (P 0).space ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2))
    (hsphere : ∀ i x, x ∈ (B i).source → (x ∈ (P 1).space ↔ B i x 1 = 0))
    (C : ↥(A \ {p 0, p 1}) → OpenPartialHomeomorph V3 V3)
    (hC : ∀ q, C q ∈ piecewiseAffineGroupoid V3)
    (hqC : ∀ q, (q : V3) ∈ (C q).source)
    (hcross : ∀ q (i : Fin 2) x, x ∈ (C q).source →
      (x ∈ (P i.castSucc).space ↔ C q x i.castSucc = 0)) :
    ∃ (R : Set V3) (K : SimplicialComplex ℝ V3)
      (M : Sum Bool (Fin 3) → SimplicialComplex ℝ V3)
      (E : Fin 2 → OpenPartialHomeomorph V3 V3)
      (V : Fin 2 → Set V3) (G : A → OpenPartialHomeomorph V3 V3),
      IsClosed R ∧ A ⊆ R ∧ A ∩ frontier R = {p 0, p 1} ∧
      A \ {p 0, p 1} ⊆ interior R ∧
      K.faces.Finite ∧ A ⊆ interior K.space ∧ K.space ⊆ W ∧
      K.space ⊆ (⋃ i, V i) ∪ interior R ∧
      (∀ i, E i ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ (E i).source ∧
        (E i).source ⊆ W ∧ E i (p i) = 0) ∧
      Pairwise (fun i j => Disjoint (E i).source (E j).source) ∧
      (∀ i x, x ∈ (E i).source →
        (x ∈ (P 0).space ↔ E i x 0 = 0 ∧ 0 ≤ E i x 2)) ∧
      (∀ i x, x ∈ (E i).source → (x ∈ (P 1).space ↔ E i x 1 = 0)) ∧
      (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (E i).source ∩ W ∧
        (∀ x ∈ V i, x ∈ R ↔ 0 ≤ E i x 2) ∧
        (∀ x ∈ V i, x ∈ frontier R ↔ E i x 2 = 0)) ∧
      (∀ i, M i ≤ K ∧ (M i).faces.Finite ∧
        ∀ f ∈ K.faces, (∀ v ∈ f, v ∈ (M i).vertices) → f ∈ (M i).faces) ∧
      (M (.inl false)).space = K.space ∩ R ∧
      (M (.inl true)).space = K.space ∩ frontier R ∧
      (∀ i, (M (.inr i)).space = K.space ∩ R ∩ (P i).space) ∧
      (M (.inr 2)).space = A ∧
      (∀ i : Fin 2, (M (.inr i.castSucc)).space = K.space ∩ (R ∩ (P i.castSucc).space)) ∧
      (∀ q, (q : V3) ∈ (G q).source ∧ (G q).source ⊆ W ∧
        G q ∈ piecewiseAffineGroupoid V3 ∧
        (∀ x ∈ (G q).source, x ∈ A ↔ x ∈ R ∧ G q x 0 = 0 ∧ G q x 1 = 0) ∧
        (∀ (i : Fin 2) x, x ∈ (G q).source →
          (x ∈ R ∩ (P i.castSucc).space ↔ x ∈ R ∧ G q x i.castSucc = 0)) ∧
        ((G q).source ⊆ interior R ∨
          (∀ x ∈ (G q).source, x ∈ R ↔ 0 ≤ G q x 2) ∧
          (∀ x ∈ (G q).source, x ∈ frontier R ↔ G q x 2 = 0))) := by
  let D : Fin 2 → Set V3 := fun i => (P i.castSucc).space
  have hpA (i : Fin 2) : p i ∈ A := hd.1 (by fin_cases i <;> simp)
  obtain ⟨E, hE, hdis, haxis, hEtriangle, hEsphere⟩ :=
    exists_disjoint_endpoint_axis_charts A D p hpne W hW (fun i => hAW (hpA i))
      hisolate B hB hpB hBp htriangle hsphere
  obtain ⟨R, K, M, V, hR, hAR, hAF, hAI, hK, hAK, hKW, hKV,
    hV, hM, hreg, hfr, hsource⟩ :=
    exists_arc_endpoint_cap_model E (fun i => (hE i).1) p
      (fun i => (hE i).2.1) (fun i => (hE i).2.2.2) hdis A hd.isCompact
      haxis hW hAW P hP
  obtain ⟨G, hG⟩ := exists_capped_paired_chart_family A R D p W hW hAW hAR hisolate
    E (fun i => (hE i).1) V (fun i => (hV i).1) (fun i => (hV i).2.1)
    (fun i x hx => ((hV i).2.2.1 hx).1)
    (fun i => (hV i).2.2.2.1) (fun i => (hV i).2.2.2.2)
    hEtriangle hEsphere hAI C hC hqC hcross
  have harc : (M (.inr 2)).space = A := by
    rw [hsource 2, hPa]
    apply inter_eq_right.mpr
    exact fun x hx => ⟨interior_subset (hAK hx), hAR hx⟩
  refine ⟨R, K, M, E, V, G, hR, hAR, hAF, hAI, hK, hAK, hKW, hKV,
    hE, hdis, hEtriangle, hEsphere, hV, hM, hreg, hfr, hsource, harc, ?_, hG⟩
  intro i
  rw [hsource i.castSucc, inter_assoc]

end PoincareConjecture.M76
