import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.EndpointCappedScene
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CoordinateSignedTube










set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1




theorem exists_endpoint_capped_tube
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
    ∃ (R : Set V3) (E : Fin 2 → OpenPartialHomeomorph V3 V3)
      (V : Fin 2 → Set V3) (T : Set V3) (b : I ≃ₜ A)
      (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ T),
      IsClosed R ∧ A ⊆ R ∧ A ∩ frontier R = {p 0, p 1} ∧
      A \ {p 0, p 1} ⊆ interior R ∧
      (∀ i, E i ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ (E i).source ∧
        (E i).source ⊆ W ∧ E i (p i) = 0) ∧
      Pairwise (fun i j => Disjoint (E i).source (E j).source) ∧
      (∀ i x, x ∈ (E i).source →
        (x ∈ (P 0).space ↔ E i x 0 = 0 ∧ 0 ≤ E i x 2)) ∧
      (∀ i x, x ∈ (E i).source → (x ∈ (P 1).space ↔ E i x 1 = 0)) ∧
      (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (E i).source ∩ W ∧
        (∀ x ∈ V i, x ∈ R ↔ 0 ≤ E i x 2) ∧
        (∀ x ∈ V i, x ∈ frontier R ↔ E i x 2 = 0)) ∧
      T ⊆ R ∩ W ∧ T ⊆ (⋃ i, V i) ∪ interior R ∧
      b.IsFinitePL ∧ (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : V3) = p 0 ∧
      (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : V3) = p 1 ∧ tube.IsFinitePL ∧
      (∀ t : I, (tube ⟨((0, 0), t), Dehn.signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), t.property⟩ : V3) = b t) ∧
      (∀ (i : Fin 2) (x : ↥(Dehn.signedTubeDiamond ×ˢ I)),
        (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet i ↔ (tube x : V3) ∈ (P i.castSucc).space) ∧
      (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
        (tube x : V3) ∈ frontier R ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1) := by
  classical
  obtain ⟨R, K, M, E, V, G, hR, hAR, hAF, hAI, hK, hAK, hKW, hKV,
    hE, hdis, hEtriangle, hEsphere, hV, hM, hreg, hfr, _, harc, hsheet, hG⟩ :=
    exists_endpoint_capped_scene P hP A p hPa hd hpne W hW hAW hisolate B hB hpB hBp
      htriangle hsphere C hC hqC hcross
  let S : Fin 2 → Set V3 := fun i => R ∩ (P i.castSucc).space
  obtain ⟨N, L, hN, hL, hNK, htube⟩ := exists_coordinate_signed_tube K hK hd hpne hAK hAR
    hAF S M (fun i => (hM i).1) (.inl false) (.inl true) (.inr 2)
    (fun i => .inr i.castSucc) hreg hfr harc hsheet (by
      intro x hx
      obtain ⟨hq, _, hGPL, hGA, hGS, hGR⟩ := hG ⟨x, hx⟩
      exact ⟨G ⟨x, hx⟩, hq, hGPL, hGA, hGS, hGR⟩)
  let : Fintype N.faces := hN.fintype
  let : ∀ i, Fintype (L i).faces := fun i => (hN.subset (hL i).1).fintype
  obtain ⟨bArc, tube, hbArc, hb0, hb1, htPL, htaxis, htsheet, htfront⟩ := htube
  let T := ((L (.inl false)).barycentricNeighborhood (L (.inr 2))).space
  have hLA : (L (.inr 2)).space = A := (hL (.inr 2)).2.1.trans harc
  let b : I ≃ₜ A := bArc.trans (Homeomorph.setCongr hLA)
  have hb : b.IsFinitePL := hbArc.trans
    (Homeomorph.isFinitePL_setCongr hLA (L (.inr 2)) (hN.subset (hL (.inr 2)).1) rfl)
  have hTKR : T ⊆ K.space ∩ R := by
    intro x hx
    have hxL : x ∈ (L (.inl false)).space :=
      (L (.inl false)).barycentricSubdivision_isSubdivision.space_eq.subset
        (space_subset_of_le ((L (.inl false)).barycentricNeighborhood_le (L (.inr 2))) hx)
    exact hreg.subset ((hL (.inl false)).2.1.subset hxL)
  refine ⟨R, E, V, T, b, tube, hR, hAR, hAF, hAI, hE, hdis, hEtriangle, hEsphere, hV,
    (fun x hx => ⟨(hTKR hx).2, hKW (hTKR hx).1⟩),
    (fun x hx => hKV (hTKR hx).1), hb, hb0, hb1, htPL, htaxis, ?_, htfront⟩
  intro i x
  exact (htsheet i x).trans (and_iff_right (hTKR (tube x).property).2)

end PoincareConjecture.M76
