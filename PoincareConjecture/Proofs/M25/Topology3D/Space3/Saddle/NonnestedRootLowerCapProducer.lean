import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleLowerCapAlignment

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_nonnested_root_lower_cap_producer
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (P : SurgeryCapProfile) (U V : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ∀ i, ContDiffOn ℝ ∞ (U i) (U i).source)
    (hUi : ∀ i, ContDiffOn ℝ ∞ (U i).symm (U i).target)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) (V i).source)
    (hVi : ∀ i, ContDiffOn ℝ ∞ (V i).symm (V i).target)
    (hUh : ∀ i p, p ∈ (U i).source →
      inner ℝ (u : E3) (U i p) = p.2)
    (hVh : ∀ i p, p ∈ (V i).source →
      inner ℝ (u : E3) (V i p) = p.2)
    (hUs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U i).source)
    (hVs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V i).source)
    (gamma : Fin 2 → ℝ) (hgamma : ∀ i, 0 < gamma i)
    (hcircle : ∀ i z,
      z ∈ Icc ((D.cap (W.label i)).cutHeight +
          (D.cap (W.label i)).removal) (W.level + gamma i) →
      V i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        range (fun theta : UnitCircle => psi (W.leg i (theta, z), 0)))
    (tau : ℝ) (htau : 0 < tau)
    (hboundary : ∀ i z, z ∈ Icc (W.level - tau) (W.level + tau) →
      (fun x : E2 => U i (x, z)) '' sphere (0 : E2) 1 =
        (fun x : E2 => V i (x, z)) '' sphere (0 : E2) 1)
    (hsame : ∀ i,
      U i '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
        V i '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)))
    (hdis : Disjoint
      (U 0 '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)))
      (U 1 '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ))))
    (R : Set E3) (hRsurface : R ⊆ range (fun q : UnitTwoSphere => psi (q, 0)))
    (hRheight : ∀ y ∈ R, W.level ≤ inner ℝ (u : E3) y)
    (O : Fin 2 → Set E3) (hO : ∀ i, IsOpen (O i))
    (hUO : ∀ i,
      U i '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) ⊆ O i) :
    ∃ eta bound : ℝ, 0 < eta ∧ eta < tau ∧ 1 ≤ bound ∧
      P.heightBound ≤ bound ∧
      ∀ lambda : Fin 2 → ℝ, (∀ i, 0 < lambda i) →
        (∀ i, lambda i * bound < eta) →
        ∃ (CU CV : Fin 2 → Set E3) (F : D3) (K : Set E3),
          (∀ i,
            CU i = P.capMap (U i) W.level 1 0 (lambda i) ''
              {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
            CV i = P.capMap (V i) W.level 1 0 (lambda i) ''
              {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}) ∧
          (∀ i, F '' CU i = CV i ∧ F.symm '' CV i = CU i) ∧
          F '' (R ∪ CU 0 ∪ CU 1) = R ∪ CV 0 ∪ CV 1 ∧
          F.symm '' (R ∪ CV 0 ∪ CV 1) = R ∪ CU 0 ∪ CU 1 ∧
          (∀ y ∈ R, F y = y ∧ F.symm y = y) ∧
          IsCompact K ∧ K ⊆ O 0 ∪ O 1 ∧
          tsupport (fun y => F y - y) ⊆ K ∧
          tsupport (fun y => F.symm y - y) ⊆ K ∧
          ∀ y, y ∉ K → F y = y ∧ F.symm y = y := by
  obtain ⟨eta, bound, heta, hetatau, hbound, hPbound, halign⟩ :=
    SaddleLowerLevelData.exists_lower_cap_alignment psi hpsi u D W P U V
      hU hUi hV hVi hUh hVh hUs hVs gamma hgamma hcircle tau htau
      hboundary hsame hdis R hRsurface hRheight O hO hUO
  refine ⟨eta, bound, heta, hetatau, hbound, hPbound, ?_⟩
  intro lambda hlambda hsmall
  dsimp only at halign
  obtain ⟨F, K, hFcap, hAlign, hAlignInv, hFix, hKcompact, hKO,
      hFsupp, hFIsupp, hKfix⟩ := halign lambda hlambda hsmall
  let CU : Fin 2 → Set E3 := fun i =>
    P.capMap (U i) W.level 1 0 (lambda i) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let CV : Fin 2 → Set E3 := fun i =>
    P.capMap (V i) W.level 1 0 (lambda i) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  refine ⟨CU, CV, F, K, ?_, hFcap, hAlign, hAlignInv, hFix, hKcompact,
    hKO, hFsupp, hFIsupp, hKfix⟩
  intro i
  exact ⟨rfl, rfl⟩

end PoincareConjecture.M25.Topology3D
