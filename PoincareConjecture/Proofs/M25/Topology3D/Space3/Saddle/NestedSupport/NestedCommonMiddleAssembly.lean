import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonMiddleIsotopy
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix NNReal

namespace PoincareConjecture.M25.Topology3D

noncomputable section

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

def nestedCommonL (u : UnitTwoSphere) := heightPlaneCoordinates u

def nestedCommonH (u : UnitTwoSphere) : E3 →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ E3 (u : E3)

def nestedCommonXi (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (rho : ℝ)
    (k : Fin 4) (t r : ℝ) : E2 :=
  J2.symm (![1, -1, -1, 1] k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
    ![1, 1, -1, -1] k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))

def nestedCommonXi3 (u : UnitTwoSphere) (c : ℝ) (gRef : D2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (rho : ℝ)
    (k : Fin 4) (t r : ℝ) : E3 :=
  (nestedCommonL u).symm (gRef (nestedCommonXi J2 rho k t r), c + t)

def nestedCommonE (u : UnitTwoSphere) (c : ℝ) (gRef : D2)
    (S : Fin 2 → Set E3) (j : Fin 2) (t : ℝ) : Set E2 :=
  {x : E2 |
    (nestedCommonL u).symm (gRef x, c + t) ∈ S j ∧ 1 ≤ ‖x‖}

def nestedCommonExt (u : UnitTwoSphere) (c : ℝ) (gRef : D2)
    (S : Fin 2 → Set E3) (j : Fin 2) (t : ℝ) : Set E3 :=
  (nestedCommonL u).symm ''
    ((gRef '' nestedCommonE u c gRef S j t) ×ˢ ({c + t} : Set ℝ))

def nestedCommonMid (u : UnitTwoSphere) (c : ℝ)
    (S : Fin 2 → Set E3) (j : Fin 2) (t : ℝ) : Set E3 :=
  S j ∩ {y : E3 | nestedCommonH u y = c + t}

def nestedCommonMidBand (u : UnitTwoSphere) (c : ℝ)
    (S : Fin 2 → Set E3) (j : Fin 2) (delta : ℝ) : Set E3 :=
  S j ∩ {y : E3 | |nestedCommonH u y - c| ≤ delta}

def nestedCommonOpenMidBand (u : UnitTwoSphere) (c : ℝ)
    (S : Fin 2 → Set E3) (j : Fin 2) (delta : ℝ) : Set E3 :=
  S j ∩ {y : E3 | |nestedCommonH u y - c| < delta}

theorem exists_saddle_nested_common_middle_assembly
    (u : UnitTwoSphere) (c rho delta : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (gRef : D2)
    (Xref Xtar : E3 → E3)
    (hXref : ContDiff ℝ ∞ Xref)
    (hXtar : ContDiff ℝ ∞ Xtar)
    (Sref Star : Set E3)
    (hSref : IsCompact Sref)
    (hStar : IsCompact Star)
    (hGraphRef : ∀ (t : ℝ), |t| < 2 * delta →
      ∀ x : E2, ‖x‖ < 2 →
        ((nestedCommonL u).symm (gRef x, c + t) ∈ Sref ↔
          t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2)))
    (hGraphTar : ∀ (t : ℝ), |t| < 2 * delta →
      ∀ x : E2, ‖x‖ < 2 →
        ((nestedCommonL u).symm (gRef x, c + t) ∈ Star ↔
          t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2)))
    (hTrackRef : ∀ (k : Fin 4) (r : ℝ),
      r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ t : ℝ, |t| < 2 * delta →
        HasDerivAt
          (fun s => nestedCommonXi3 u c gRef J2 rho k s r)
          (Xref (nestedCommonXi3 u c gRef J2 rho k t r)) t)
    (hTrackTar : ∀ (k : Fin 4) (r : ℝ),
      r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ t : ℝ, |t| < 2 * delta →
        HasDerivAt
          (fun s => nestedCommonXi3 u c gRef J2 rho k s r)
          (Xtar (nestedCommonXi3 u c gRef J2 rho k t r)) t)
    (Tref Ttar : ℝ → ℝ → D3)
    (hTrefSelf : ∀ (s : ℝ) (y : E3), Tref s s y = y)
    (hTtarSelf : ∀ (s : ℝ) (y : E3), Ttar s s y = y)
    (hTrefTrack : ∀ (s : ℝ), |s| < 2 * delta →
      ∀ y ∈ nestedCommonExt u c gRef (fun _ : Fin 2 => Sref) 0 s,
        ∀ t : ℝ, |t| < 2 * delta →
          HasDerivAt (fun a => Tref s a y)
            (Xref (Tref s t y)) t)
    (hTtarTrack : ∀ (s : ℝ), |s| < 2 * delta →
      ∀ y ∈ nestedCommonExt u c gRef (fun _ : Fin 2 => Star) 1 s,
        ∀ t : ℝ, |t| < 2 * delta →
          HasDerivAt (fun a => Ttar s a y)
            (Xtar (Ttar s t y)) t)
    (hTrefImage : ∀ (s t : ℝ), |s| ≤ 2 * delta → |t| ≤ 2 * delta →
      (Tref s t) '' nestedCommonExt u c gRef (fun _ : Fin 2 => Sref) 0 s =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Sref) 0 t ∧
      (Tref s t).symm '' nestedCommonExt u c gRef (fun _ : Fin 2 => Sref) 0 t =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Sref) 0 s)
    (hTtarImage : ∀ (s t : ℝ), |s| ≤ 2 * delta → |t| ≤ 2 * delta →
      (Ttar s t) '' nestedCommonExt u c gRef (fun _ : Fin 2 => Star) 1 s =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Star) 1 t ∧
      (Ttar s t).symm '' nestedCommonExt u c gRef (fun _ : Fin 2 => Star) 1 t =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Star) 1 s)
    (J : ℝ → D2) (CJ : Set E2) (hCJ : IsCompact CJ)
    (hJ : ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2))
    (hJinv : ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2))
    (hJzero : ∀ s : ℝ, s ≤ 0 → ∀ y : E2,
      J s y = y ∧ (J s).symm y = y)
    (hJone : ∀ s : ℝ, 1 ≤ s → ∀ y : E2,
      J s y = J 1 y ∧ (J s).symm y = (J 1).symm y)
    (hJsupport : ∀ s : ℝ,
      tsupport (fun y : E2 => J s y - y) ⊆ CJ ∧
      tsupport (fun y : E2 => (J s).symm y - y) ⊆ CJ)
    (hJdisc : gRef '' closedBall (0 : E2) 1 ⊆ CJᶜ)
    (hJimage :
      (J 1) '' (gRef '' nestedCommonE u c gRef
        (fun _ : Fin 2 => Sref) 0 0) =
          gRef '' nestedCommonE u c gRef
            (fun _ : Fin 2 => Star) 1 0 ∧
      (J 1).symm '' (gRef '' nestedCommonE u c gRef
        (fun _ : Fin 2 => Star) 1 0) =
          gRef '' nestedCommonE u c gRef
            (fun _ : Fin 2 => Sref) 0 0) :
    ∃ (e : ℝ) (G : ℝ → D3) (C3 : Set E3),
      0 < e ∧ e < 1 / 512 ∧ IsCompact C3 ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (G p.1).symm p.2) ∧
      (∀ y : E3, G 0 y = y ∧ (G 0).symm y = y) ∧
      (∀ (s : ℝ) (y : E3),
        nestedCommonH u (G s y) = nestedCommonH u y ∧
        nestedCommonH u ((G s).symm y) = nestedCommonH u y) ∧
      (∀ s : ℝ,
        tsupport (fun y : E3 => G s y - y) ⊆ C3 ∧
        tsupport (fun y : E3 => (G s).symm y - y) ⊆ C3) ∧
      (∀ (s : ℝ) (x : E2) (z : ℝ), ‖x‖ ≤ 1 + 2 * e →
        G s ((nestedCommonL u).symm (gRef x, z)) =
            (nestedCommonL u).symm (gRef x, z) ∧
        (G s).symm ((nestedCommonL u).symm (gRef x, z)) =
            (nestedCommonL u).symm (gRef x, z)) ∧
      (∀ (t : ℝ), |t| ≤ delta →
        G 1 '' nestedCommonMid u c (fun _ : Fin 2 => Sref) 0 t =
            nestedCommonMid u c (fun _ : Fin 2 => Star) 1 t ∧
        (G 1).symm '' nestedCommonMid u c (fun _ : Fin 2 => Star) 1 t =
            nestedCommonMid u c (fun _ : Fin 2 => Sref) 0 t) ∧
      G 1 '' nestedCommonMidBand u c (fun _ : Fin 2 => Sref) 0 delta =
          nestedCommonMidBand u c (fun _ : Fin 2 => Star) 1 delta ∧
      (G 1).symm '' nestedCommonMidBand u c (fun _ : Fin 2 => Star) 1 delta =
          nestedCommonMidBand u c (fun _ : Fin 2 => Sref) 0 delta ∧
      G 1 '' nestedCommonOpenMidBand u c (fun _ : Fin 2 => Sref) 0 delta =
          nestedCommonOpenMidBand u c (fun _ : Fin 2 => Star) 1 delta ∧
      (G 1).symm '' nestedCommonOpenMidBand u c (fun _ : Fin 2 => Star) 1 delta =
          nestedCommonOpenMidBand u c (fun _ : Fin 2 => Sref) 0 delta := by
  let X : Fin 2 → E3 → E3 := ![Xref, Xtar]
  let S : Fin 2 → Set E3 := ![Sref, Star]
  let T : Fin 2 → ℝ → ℝ → D3 := ![Tref, Ttar]
  have hX : ∀ j : Fin 2, ContDiff ℝ ∞ (X j) := by
    intro j
    fin_cases j
    · exact hXref
    · exact hXtar
  have hS : ∀ j : Fin 2, IsCompact (S j) := by
    intro j
    fin_cases j
    · exact hSref
    · exact hStar
  have hGraph : ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
      ∀ x : E2, ‖x‖ < 2 →
        ((nestedCommonL u).symm (gRef x, c + t) ∈ S j ↔
          t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2)) := by
    intro j t ht x hx
    fin_cases j
    · simpa [S] using hGraphRef t ht x hx
    · simpa [S] using hGraphTar t ht x hx
  have hTrack : ∀ (j : Fin 2) (k : Fin 4) (r : ℝ),
      r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ t : ℝ, |t| < 2 * delta →
        HasDerivAt (fun s => nestedCommonXi3 u c gRef J2 rho k s r)
          (X j (nestedCommonXi3 u c gRef J2 rho k t r)) t := by
    intro j k r hr t ht
    fin_cases j
    · exact hTrackRef k r hr t ht
    · exact hTrackTar k r hr t ht
  have hTself : ∀ (j : Fin 2) (s : ℝ) (y : E3), T j s s y = y := by
    intro j s y
    fin_cases j
    · exact hTrefSelf s y
    · exact hTtarSelf s y
  have hTtrack : ∀ (j : Fin 2) (s : ℝ), |s| < 2 * delta →
      ∀ y ∈ nestedCommonExt u c gRef S j s, ∀ t : ℝ,
        |t| < 2 * delta →
          HasDerivAt (fun a => T j s a y) (X j (T j s t y)) t := by
    intro j s hs y hy t ht
    fin_cases j
    · simpa [X, S, T] using hTrefTrack s hs y hy t ht
    · simpa [X, S, T] using hTtarTrack s hs y hy t ht
  have hTimage : ∀ (j : Fin 2) (s t : ℝ),
      |s| ≤ 2 * delta → |t| ≤ 2 * delta →
      (T j s t) '' nestedCommonExt u c gRef S j s =
          nestedCommonExt u c gRef S j t ∧
      (T j s t).symm '' nestedCommonExt u c gRef S j t =
          nestedCommonExt u c gRef S j s := by
    intro j s t hs ht
    fin_cases j
    · change (Tref s t) '' nestedCommonExt u c gRef
          (fun _ : Fin 2 => Sref) 0 s =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Sref) 0 t ∧
        (Tref s t).symm '' nestedCommonExt u c gRef
          (fun _ : Fin 2 => Sref) 0 t =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Sref) 0 s
      exact hTrefImage s t hs ht
    · change (Ttar s t) '' nestedCommonExt u c gRef
          (fun _ : Fin 2 => Star) 1 s =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Star) 1 t ∧
        (Ttar s t).symm '' nestedCommonExt u c gRef
          (fun _ : Fin 2 => Star) 1 t =
          nestedCommonExt u c gRef (fun _ : Fin 2 => Star) 1 s
      exact hTtarImage s t hs ht
  have hJimage' :
      (J 1) '' (gRef '' nestedCommonE u c gRef S 0 0) =
          gRef '' nestedCommonE u c gRef S 1 0 ∧
      (J 1).symm '' (gRef '' nestedCommonE u c gRef S 1 0) =
          gRef '' nestedCommonE u c gRef S 0 0 := by
    change (J 1) '' (gRef '' nestedCommonE u c gRef
      (fun _ : Fin 2 => Sref) 0 0) =
        gRef '' nestedCommonE u c gRef (fun _ : Fin 2 => Star) 1 0 ∧
      (J 1).symm '' (gRef '' nestedCommonE u c gRef
        (fun _ : Fin 2 => Star) 1 0) =
        gRef '' nestedCommonE u c gRef (fun _ : Fin 2 => Sref) 0 0
    exact hJimage
  simpa [nestedCommonL, nestedCommonH, nestedCommonXi, nestedCommonXi3,
    nestedCommonE, nestedCommonExt, nestedCommonMid, nestedCommonMidBand,
    nestedCommonOpenMidBand, X, S, T] using
    (exists_saddle_common_middle_isotopy u c rho delta hrho hdelta hsmall J2 hJ2
      gRef X hX S hS hGraph hTrack T hTself hTtrack hTimage J CJ hCJ hJ hJinv
      hJzero hJone hJsupport hJdisc hJimage')

end
end PoincareConjecture.M25.Topology3D
