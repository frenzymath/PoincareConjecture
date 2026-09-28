import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleLowerLevelBand
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsPairedAlignment











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D




theorem SaddleLowerLevelData.exists_fixed_lower_tube_band
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (V : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (gamma : Fin 2 → ℝ) (hgamma : ∀ i, 0 < gamma i)
    (tau : ℝ) (htau : 0 < tau)
    (hcircle : ∀ i z,
      z ∈ Icc ((D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal)
        (W.level + gamma i) →
      V i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        range (fun theta : UnitCircle => psi (W.leg i (theta, z), 0))) :
    ∃ eta : ℝ, 0 < eta ∧ eta < tau ∧
      (∀ i, eta < gamma i ∧
        (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal < W.level - eta) ∧
      (∀ i z, z ∈ Icc (W.level - eta) (W.level + eta) →
        V i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
          range (fun theta : UnitCircle => psi (W.leg i (theta, z), 0))) ∧
      ∀ y ∈ range (fun q : UnitTwoSphere => psi (q, 0)),
        inner ℝ (u : E3) y ∈ Icc (W.level - eta) (W.level + eta) →
          ∃ i : Fin 2, y ∈ V i '' (sphere (0 : E2) 1 ×ˢ
            ({inner ℝ (u : E3) y} : Set ℝ)) := by
  let ell : Fin 2 → ℝ := fun i =>
    (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal
  have hell (i : Fin 2) : ell i < W.level := by
    simpa only [ell, W.label_lower i, one_mul] using
      W.lower_seams_lt_level (W.label i) (W.label_lower i)
  let b : Fin 2 → ℝ := fun i => min (gamma i) (W.level - ell i)
  have hb (i : Fin 2) : 0 < b i := lt_min (hgamma i) (sub_pos.mpr (hell i))
  let m := min tau (min (b 0) (b 1))
  let a := m / 2
  have hm : 0 < m := lt_min htau (lt_min (hb 0) (hb 1))
  have ha : 0 < a := half_pos hm
  have ham : a < m := half_lt_self hm
  have hata : a < tau := ham.trans_le (min_le_left _ _)
  have hab (i : Fin 2) : a < b i := by
    have hh : a < min (b 0) (b 1) := ham.trans_le (min_le_right _ _)
    fin_cases i
    · exact hh.trans_le (min_le_left _ _)
    · exact hh.trans_le (min_le_right _ _)
  have hagamma (i : Fin 2) : a < gamma i := (hab i).trans_le (min_le_left _ _)
  have hagap (i : Fin 2) : a < W.level - ell i :=
    (hab i).trans_le (min_le_right _ _)
  have hacircle (i : Fin 2) (z : ℝ)
      (hz : z ∈ Icc (W.level - a) (W.level + a)) :
      V i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        range (fun theta : UnitCircle => psi (W.leg i (theta, z), 0)) := by
    apply hcircle i z
    change ell i ≤ z ∧ z ≤ W.level + gamma i
    constructor
    · linarith [hz.1, hagap i]
    · linarith [hz.2, hagamma i]
  obtain ⟨eta, heta, hetaa, hcover⟩ :=
    W.exists_physical_level_band psi hpsi u D V a ha hacircle
  refine ⟨eta, heta, hetaa.trans hata, ?_, ?_, hcover⟩
  · intro i
    refine ⟨hetaa.trans (hagamma i), ?_⟩
    change ell i < W.level - eta
    linarith [hagap i]
  · intro i z hz
    exact hacircle i z ⟨by linarith [hz.1], by linarith [hz.2]⟩




theorem SaddleLowerLevelData.exists_lower_cap_alignment
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (P : SurgeryCapProfile) (U V : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ∀ i, ContDiffOn ℝ ∞ (U i) (U i).source)
    (hUi : ∀ i, ContDiffOn ℝ ∞ (U i).symm (U i).target)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) (V i).source)
    (hVi : ∀ i, ContDiffOn ℝ ∞ (V i).symm (V i).target)
    (hUh : ∀ i p, p ∈ (U i).source → inner ℝ (u : E3) (U i p) = p.2)
    (hVh : ∀ i p, p ∈ (V i).source → inner ℝ (u : E3) (V i p) = p.2)
    (hUs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U i).source)
    (hVs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V i).source)
    (gamma : Fin 2 → ℝ) (hgamma : ∀ i, 0 < gamma i)
    (hcircle : ∀ i z,
      z ∈ Icc ((D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal)
        (W.level + gamma i) →
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
    (hUO : ∀ i, U i '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) ⊆ O i) :
    ∃ eta bound : ℝ, 0 < eta ∧ eta < tau ∧ 1 ≤ bound ∧ P.heightBound ≤ bound ∧
      ∀ lambda : Fin 2 → ℝ, (∀ i, 0 < lambda i) → (∀ i, lambda i * bound < eta) →
        let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
        let CU := fun i => P.capMap (U i) W.level 1 0 (lambda i) '' Qminus
        let CV := fun i => P.capMap (V i) W.level 1 0 (lambda i) '' Qminus
        ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          ∃ K : Set E3,
            (∀ i, F '' CU i = CV i ∧ F.symm '' CV i = CU i) ∧
            F '' (R ∪ CU 0 ∪ CU 1) = R ∪ CV 0 ∪ CV 1 ∧
            F.symm '' (R ∪ CV 0 ∪ CV 1) = R ∪ CU 0 ∪ CU 1 ∧
            (∀ y ∈ R, F y = y ∧ F.symm y = y) ∧
            IsCompact K ∧ K ⊆ O 0 ∪ O 1 ∧
            tsupport (fun y => F y - y) ⊆ K ∧
            tsupport (fun y => F.symm y - y) ⊆ K ∧
            ∀ y, y ∉ K → F y = y ∧ F.symm y = y := by
  obtain ⟨epsilon, hepsilon, hepsilontau, _hseams, _hcircles, hcover⟩ :=
    W.exists_fixed_lower_tube_band psi hpsi u D V gamma hgamma tau htau hcircle
  have hboundary' (i : Fin 2) (z : ℝ)
      (hz : z ∈ Icc (W.level - epsilon) (W.level + epsilon)) :
      (fun x : E2 => U i (x, z)) '' sphere (0 : E2) 1 =
        (fun x : E2 => V i (x, z)) '' sphere (0 : E2) 1 :=
    hboundary i z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨eta, bound, heta, hetaepsilon, hbound, hPbound, halign⟩ :=
    exists_stackNonnestedLowerCapAlignment P U V hU hUi hV hVi u hUh hVh hUs hVs
      W.level epsilon hepsilon hboundary' hsame hdis R hRheight
      (fun y hy => hcover y (hRsurface hy)) O hO hUO
  exact ⟨eta, bound, heta, hetaepsilon.trans hepsilontau, hbound, hPbound, halign⟩

end PoincareConjecture.M25.Topology3D
