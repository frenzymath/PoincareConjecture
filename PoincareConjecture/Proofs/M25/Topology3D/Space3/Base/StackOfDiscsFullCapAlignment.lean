import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsPhysicalAlignment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsOriginalProfileAlignment

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackOriginalCapAlignment_in_height_band
    (P : SurgeryCapProfile) (U V : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ContDiffOn ℝ ∞ U U.source) (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source) (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (u : UnitTwoSphere)
    (hUh : ∀ p ∈ U.source, inner ℝ (u : E3) (U p) = p.2)
    (hVh : ∀ p ∈ V.source, inner ℝ (u : E3) (V p) = p.2)
    (hUs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ U.source)
    (hVs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ V.source)
    (I : Set ℝ) (hI : IsCompact I)
    (hboundary : ∀ z ∈ I,
      (fun x : E2 => U (x, z)) '' sphere (0 : E2) 1 =
        (fun x : E2 => V (x, z)) '' sphere (0 : E2) 1)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (hkI : ∀ z, k z ∈ I)
    (L A a b B R : ℝ)
    (hLA : L < A) (hAa : A < a) (hab : a < b) (hbB : b < B) (hBR : B < R)
    (hkfix : ∀ z ∈ Icc A B, k z = z)
    (O : Set E3) (hO : IsOpen O)
    (hcircleO : V '' (sphere (0 : E2) 1 ×ˢ Icc A B) ⊆ O) :
    ∃ bound : ℝ, 1 ≤ bound ∧ P.heightBound ≤ bound ∧
      ∀ s sigma lambda eta : ℝ, |sigma| = 1 → 0 < lambda → lambda * bound < eta →
        a ≤ s - eta → s + eta ≤ b →
        ∀ OU OV : Set E3, IsOpen OU → IsOpen OV →
          U '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ OU →
          V '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ OV →
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
            ∃ K : Set E3,
              F '' (P.capMap U s sigma 0 lambda '' Qminus) =
                P.capMap V s sigma 0 lambda '' Qminus ∧
              F.symm '' (P.capMap V s sigma 0 lambda '' Qminus) =
                P.capMap U s sigma 0 lambda '' Qminus ∧
              IsCompact K ∧ K ⊆ OU ∪ (O ∩ {y | inner ℝ (u : E3) y ∈ Ioo A B}) ∪ OV ∧
              tsupport (fun y => F y - y) ⊆ K ∧
              tsupport (fun y => F.symm y - y) ⊆ K ∧
              (∀ y, y ∉ K → F y = y ∧ F.symm y = y) ∧
              ∀ y, (y ∉ O ∨ inner ℝ (u : E3) y ∉ Ioo A B ∨
                y ∈ V '' (sphere (0 : E2) 1 ×ˢ Icc A B)) →
                (0 ≤ sigma * (inner ℝ (u : E3) y - s) ∨ (y ∉ OU ∧ y ∉ OV)) →
                F y = y ∧ F.symm y = y := by
  obtain ⟨delta, hd, hdq, Psi, S, hS, hSO, hSband, _hPsi, _hPsii, _hPsi0,
      _hSupport, hFix, _hHeight, hCircle, hCaps⟩ :=
    exists_stackPhysicalCanonicalCapAlignment U V hU hUi hV hVi u hUh hVh I hI
      (fun _ hp => hUs ⟨hp.1, mem_univ _⟩)
      (fun _ hp => hVs ⟨hp.1, mem_univ _⟩) hboundary k hk hkI
      L A a b B R hLA hAa hab hbB hBR hkfix O hO hcircleO
  let rFlat := 1 - delta / 2
  let rOne := 1 - delta / 4
  let v0 := delta / 16
  let v1 := delta / 8
  have hrFlat : 0 < rFlat := by dsimp only [rFlat]; linarith only [hdq]
  have hrann : 1 - delta < rFlat := by dsimp only [rFlat]; linarith only [hd]
  have hradii : rFlat < rOne := by dsimp only [rFlat, rOne]; linarith only [hd]
  have hrOne : rOne < 1 := by dsimp only [rOne]; linarith only [hd]
  have hv0 : 0 < v0 := by dsimp only [v0]; linarith only [hd]
  have hv01 : v0 < v1 := by dsimp only [v0, v1]; linarith only [hd]
  have hv1 : v1 < 1 := by dsimp only [v1]; linarith only [hdq]
  have hgap : v1 ^ 2 + rOne ^ 2 < 1 := by
    dsimp only [v1, rOne]
    nlinarith [mul_lt_mul_of_pos_left hdq hd]
  obtain ⟨B0, hB0, _hPathBound, hrestore⟩ :=
    exists_stackOriginalProfileAlignment P rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1
  let bound := max B0 P.heightBound
  refine ⟨bound, hB0.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro s sigma lambda eta hsign hlambda hsmall hleft hright OU OV hOU hOV hUstack hVstack
  have hsmall0 : lambda * B0 < eta :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_left _ _) hlambda.le) hsmall
  have hleta : lambda < eta := by
    calc
      lambda = lambda * 1 := (mul_one _).symm
      _ ≤ lambda * B0 := mul_le_mul_of_nonneg_left hB0 hlambda.le
      _ < eta := hsmall0
  obtain ⟨_hYU, _hYV, hcap, _hcapi⟩ :=
    hCaps s sigma lambda eta rFlat rOne v0 v1 hsign hlambda hleta hleft hright
      hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
  obtain ⟨F, K, hf, hi, hK, hKsub, hsupport, hisupport, hboth, hprotected⟩ :=
    hrestore U V hUs hVs hU hUi hV hVi u hUh hVh s sigma lambda eta
      hsign hlambda hsmall0 OU OV hOU hOV hUstack hVstack (Psi 1) hcap S hS (hFix 1)
  refine ⟨F, K, hf, hi, hK, ?_, hsupport, hisupport, hboth, ?_⟩
  · exact hKsub.trans (union_subset_union
      (union_subset_union subset_rfl (fun y hy => ⟨hSO hy, hSband hy⟩)) subset_rfl)
  · intro y hcanonical hprofile
    have hfixed : Psi 1 y = y := by
      rcases hcanonical with hout | hheight | hcircle
      · exact (hFix 1 y (fun hy => hout (hSO hy))).1
      · exact (hFix 1 y (fun hy => hheight (hSband hy))).1
      · obtain ⟨⟨q, z⟩, hqz, rfl⟩ := hcircle
        exact (hCircle 1 z hqz.2 q hqz.1).1
    exact hprotected y hfixed hprofile

theorem exists_stackOriginalCapAlignment
    (P : SurgeryCapProfile) (U V : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ContDiffOn ℝ ∞ U U.source) (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source) (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (u : UnitTwoSphere)
    (hUh : ∀ p ∈ U.source, inner ℝ (u : E3) (U p) = p.2)
    (hVh : ∀ p ∈ V.source, inner ℝ (u : E3) (V p) = p.2)
    (hUs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ U.source)
    (hVs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ V.source)
    (I : Set ℝ) (hI : IsCompact I)
    (hboundary : ∀ z ∈ I,
      (fun x : E2 => U (x, z)) '' sphere (0 : E2) 1 =
        (fun x : E2 => V (x, z)) '' sphere (0 : E2) 1)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (hkI : ∀ z, k z ∈ I)
    (L A a b B R : ℝ)
    (hLA : L < A) (hAa : A < a) (hab : a < b) (hbB : b < B) (hBR : B < R)
    (hkfix : ∀ z ∈ Icc A B, k z = z)
    (O : Set E3) (hO : IsOpen O)
    (hcircleO : V '' (sphere (0 : E2) 1 ×ˢ Icc A B) ⊆ O) :
    ∃ bound : ℝ, 1 ≤ bound ∧ P.heightBound ≤ bound ∧
      ∀ s sigma lambda eta : ℝ, |sigma| = 1 → 0 < lambda → lambda * bound < eta →
        a ≤ s - eta → s + eta ≤ b →
        ∀ OU OV : Set E3, IsOpen OU → IsOpen OV →
          U '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ OU →
          V '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ OV →
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
            ∃ K : Set E3,
              F '' (P.capMap U s sigma 0 lambda '' Qminus) =
                P.capMap V s sigma 0 lambda '' Qminus ∧
              F.symm '' (P.capMap V s sigma 0 lambda '' Qminus) =
                P.capMap U s sigma 0 lambda '' Qminus ∧
              IsCompact K ∧ K ⊆ OU ∪ O ∪ OV ∧
              tsupport (fun y => F y - y) ⊆ K ∧
              tsupport (fun y => F.symm y - y) ⊆ K ∧
              (∀ y, y ∉ K → F y = y ∧ F.symm y = y) ∧
              ∀ y, (y ∉ O ∨ y ∈ V '' (sphere (0 : E2) 1 ×ˢ Icc A B)) →
                (0 ≤ sigma * (inner ℝ (u : E3) y - s) ∨ (y ∉ OU ∧ y ∉ OV)) →
                F y = y ∧ F.symm y = y := by
  obtain ⟨bound, hbound, hPbound, h⟩ :=
    exists_stackOriginalCapAlignment_in_height_band P U V hU hUi hV hVi
      u hUh hVh hUs hVs I hI hboundary k hk hkI
      L A a b B R hLA hAa hab hbB hBR hkfix O hO hcircleO
  refine ⟨bound, hbound, hPbound, ?_⟩
  intro s sigma lambda eta hsign hlambda hsmall hleft hright OU OV hOU hOV hUstack hVstack
  obtain ⟨F, K, hf, hi, hK, hKsub, hsupport, hisupport, hboth, hprotected⟩ :=
    h s sigma lambda eta hsign hlambda hsmall hleft hright OU OV hOU hOV hUstack hVstack
  refine ⟨F, K, hf, hi, hK, ?_, hsupport, hisupport, hboth, ?_⟩
  · exact hKsub.trans (union_subset_union
      (union_subset_union subset_rfl inter_subset_left) subset_rfl)
  · intro y hcanonical hprofile
    apply hprotected y ?_ hprofile
    rcases hcanonical with hout | hcircle
    · exact Or.inl hout
    · exact Or.inr (Or.inr hcircle)

end PoincareConjecture.M25.Topology3D
