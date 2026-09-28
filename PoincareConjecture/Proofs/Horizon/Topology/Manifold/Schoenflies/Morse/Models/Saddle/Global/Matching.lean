import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.RelativeSpatial
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Levels.Description
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.Parametric
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.IntervalExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.GlobalFilling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleFamilies
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.DisjointSupport

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P2 := Real × E2
local notation "IR2" => 𝓘(Real, Real × Real)

private theorem contDiff_planar_family_symm
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : ContDiff Real ∞ (fun z : P2 => Q z.1 z.2)) :
    ContDiff Real ∞ (fun z : P2 => (Q z.1).symm z.2) := by
  have hm : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : P2 => Q z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hQ.contMDiff
  have hi := Poincare.Manifold.contMDiff_diffeomorph_family_symm Q hm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hi
  exact hi.contDiff

theorem exists_smooth_height_retraction (c : Real) {r R : Real}
    (hr : 0 < r) (hrR : r < R) :
    ∃ σ : Real → Real, ContDiff Real ∞ σ ∧
      (∀ t, σ t ∈ closedBall c R) ∧
      ∀ t ∈ closedBall c r, σ t = t := by
  let χ : ContDiffBump c := ⟨r, R, hr, hrR⟩
  let σ : Real → Real := fun t => χ t * (t - c) + c
  refine ⟨σ, (χ.contDiff.mul (contDiff_id.sub contDiff_const)).add contDiff_const, ?_, ?_⟩
  · intro t
    change |χ t * (t - c) + c - c| ≤ R
    rw [add_sub_cancel_right, abs_mul, abs_of_nonneg χ.nonneg]
    by_cases ht : t ∈ closedBall c R
    · exact (mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg (t - c))).trans
        (by simpa only [one_mul, mem_closedBall, Real.dist_eq] using ht)
    · rw [χ.zero_of_le_dist (le_of_lt (not_le.mp ht)), zero_mul]
      exact (hr.trans hrR).le
  · intro t ht
    change χ t * (t - c) + c = t
    rw [χ.one_of_mem_closedBall ht, one_mul, sub_add_cancel]

theorem exists_planar_family_gluing
    (L R : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hL : ContDiff Real ∞ (fun z : P2 => L z.1 z.2))
    (hR : ContDiff Real ∞ (fun z : P2 => R z.1 z.2))
    {a b : Real} (hab : a < b)
    (heq : ∀ t ∈ Ioo a b, ∀ x, L t x = R t x)
    {K : Set E2} (hK : IsCompact K)
    (hLfix : ∀ t x, x ∉ K → L t x = x)
    (hRfix : ∀ t x, x ∉ K → R t x = x) :
    ∃ P : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : P2 => P z.1 z.2) ∧
      ContDiff Real ∞ (fun z : P2 => (P z.1).symm z.2) ∧
      (∃ C : Set E2, IsCompact C ∧ ∀ t x, x ∉ C → P t x = x) ∧
      (∀ t, t < b → ∀ x, P t x = L t x) ∧
      ∀ t, a < t → ∀ x, P t x = R t x := by
  classical
  let m := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  let P (t : Real) := if t ≤ m then L t else R t
  have hPL (t : Real) (ht : t < b) (x : E2) : P t x = L t x := by
    dsimp only [P]
    split_ifs with htm
    · rfl
    · exact (heq t ⟨ham.trans (lt_of_not_ge htm), ht⟩ x).symm
  have hPR (t : Real) (ht : a < t) (x : E2) : P t x = R t x := by
    dsimp only [P]
    split_ifs with htm
    · exact heq t ⟨ht, htm.trans_lt hmb⟩ x
    · rfl
  have hPs : ContDiff Real ∞ (fun z : P2 => P z.1 z.2) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 < b
    · apply hL.contDiffAt.congr_of_eventuallyEq
      have hn : {y : P2 | y.1 < b} ∈ 𝓝 z :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hz
      filter_upwards [hn] with y hy using hPL y.1 hy y.2
    · apply hR.contDiffAt.congr_of_eventuallyEq
      have hn : {y : P2 | a < y.1} ∈ 𝓝 z :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds (hab.trans_le (le_of_not_gt hz))
      filter_upwards [hn] with y hy using hPR y.1 hy y.2
  refine ⟨P, hPs, contDiff_planar_family_symm P hPs, ⟨K, hK, ?_⟩, hPL, hPR⟩
  intro t x hx
  dsimp only [P]
  split_ifs
  · exact hLfix t x hx
  · exact hRfix t x hx

theorem exists_parametric_planar_family_gluing
    (L R : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hL : ContDiff Real ∞ (fun z : Real × Real × E2 => L z.1 z.2.1 z.2.2))
    (hR : ContDiff Real ∞ (fun z : Real × Real × E2 => R z.1 z.2.1 z.2.2))
    (hLi : ContDiff Real ∞ (fun z : Real × Real × E2 => (L z.1 z.2.1).symm z.2.2))
    (hRi : ContDiff Real ∞ (fun z : Real × Real × E2 => (R z.1 z.2.1).symm z.2.2))
    (hLzero : ∀ t x, L 0 t x = x) (hRzero : ∀ t x, R 0 t x = x)
    {a b : Real} (hab : a < b)
    (heq : ∀ t ∈ Ioo a b, ∀ u x, L u t x = R u t x)
    {K : Set E2} (hK : IsCompact K)
    (hLfix : ∀ u t x, x ∉ K → L u t x = x)
    (hRfix : ∀ u t x, x ∉ K → R u t x = x) :
    ∃ P : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : Real × Real × E2 => P z.1 z.2.1 z.2.2) ∧
      ContDiff Real ∞ (fun z : Real × Real × E2 => (P z.1 z.2.1).symm z.2.2) ∧
      (∀ t x, P 0 t x = x) ∧
      (∃ C : Set E2, IsCompact C ∧ ∀ u t x, x ∉ C → P u t x = x) ∧
      (∀ t, t < b → ∀ u, P u t = L u t) ∧
      ∀ t, a < t → ∀ u, P u t = R u t := by
  classical
  let m := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  let P (u t : Real) := if t ≤ m then L u t else R u t
  have hPL (t : Real) (ht : t < b) (u : Real) : P u t = L u t := by
    dsimp only [P]
    split_ifs with htm
    · rfl
    · exact (Diffeomorph.ext (heq t ⟨ham.trans (lt_of_not_ge htm), ht⟩ u)).symm
  have hPR (t : Real) (ht : a < t) (u : Real) : P u t = R u t := by
    dsimp only [P]
    split_ifs with htm
    · exact Diffeomorph.ext (heq t ⟨ht, htm.trans_lt hmb⟩ u)
    · rfl
  have hPs : ContDiff Real ∞ (fun z : Real × Real × E2 => P z.1 z.2.1 z.2.2) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.2.1 < b
    · apply hL.contDiffAt.congr_of_eventuallyEq
      have hn : {y : Real × Real × E2 | y.2.1 < b} ∈ 𝓝 z :=
        (isOpen_lt (continuous_fst.comp continuous_snd) continuous_const).mem_nhds hz
      filter_upwards [hn] with y hy using congrArg (fun D => D y.2.2) (hPL y.2.1 hy y.1)
    · apply hR.contDiffAt.congr_of_eventuallyEq
      have hn : {y : Real × Real × E2 | a < y.2.1} ∈ 𝓝 z :=
        (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds
          (hab.trans_le (le_of_not_gt hz))
      filter_upwards [hn] with y hy using congrArg (fun D => D y.2.2) (hPR y.2.1 hy y.1)
  have hPis : ContDiff Real ∞
      (fun z : Real × Real × E2 => (P z.1 z.2.1).symm z.2.2) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.2.1 < b
    · apply hLi.contDiffAt.congr_of_eventuallyEq
      have hn : {y : Real × Real × E2 | y.2.1 < b} ∈ 𝓝 z :=
        (isOpen_lt (continuous_fst.comp continuous_snd) continuous_const).mem_nhds hz
      filter_upwards [hn] with y hy
      rw [hPL y.2.1 hy]
    · apply hRi.contDiffAt.congr_of_eventuallyEq
      have hn : {y : Real × Real × E2 | a < y.2.1} ∈ 𝓝 z :=
        (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds
          (hab.trans_le (le_of_not_gt hz))
      filter_upwards [hn] with y hy
      rw [hPR y.2.1 hy]
  refine ⟨P, hPs, hPis, ?_, ⟨K, hK, ?_⟩, hPL, hPR⟩
  · intro t x
    dsimp only [P]
    split_ifs
    · exact hLzero t x
    · exact hRzero t x
  · intro u t x hx
    dsimp only [P]
    split_ifs
    · exact hLfix u t x hx
    · exact hRfix u t x hx

theorem exists_matching_extension_along_regular_transports
    {ι : Type*} (A B : ι → Real → Set E2) (A₀ B₀ : ι → Set E2)
    (U V Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hU : ContDiff Real ∞ (fun z : P2 => U z.1 z.2))
    (hV : ContDiff Real ∞ (fun z : P2 => V z.1 z.2))
    (hQ : ContDiff Real ∞ (fun z : P2 => Q z.1 z.2))
    {K : Set E2} (hK : IsCompact K)
    (hUfix : ∀ t x, x ∉ K → U t x = x)
    (hVfix : ∀ t x, x ∉ K → V t x = x)
    (hQfix : ∀ t x, x ∉ K → Q t x = x)
    (I J : Set Real)
    (hUA : ∀ i t, t ∈ I → U t '' A₀ i = A i t)
    (hVB : ∀ i t, t ∈ I → V t '' B₀ i = B i t)
    (hmatch : ∀ i t, t ∈ J → Q t '' A i t = B i t)
    (σ : Real → Real) (hσ : ContDiff Real ∞ σ)
    (hσIJ : ∀ t ∈ I, σ t ∈ I ∩ J) :
    ∃ P : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : P2 => P z.1 z.2) ∧
      ContDiff Real ∞ (fun z : P2 => (P z.1).symm z.2) ∧
      (∃ C : Set E2, IsCompact C ∧ ∀ t x, x ∉ C → P t x = x) ∧
      (∀ i t, t ∈ I → P t '' A i t = B i t) ∧
      ∀ t, σ t = t → ∀ x, P t x = Q t x := by
  let P (t : Real) :=
    ((((U t).symm.trans (U (σ t))).trans (Q (σ t))).trans (V (σ t)).symm).trans (V t)
  have hUi := contDiff_planar_family_symm U hU
  have hVi := contDiff_planar_family_symm V hV
  have hs : ContDiff Real ∞ (fun z : P2 => σ z.1) := hσ.comp contDiff_fst
  have hPs : ContDiff Real ∞ (fun z : P2 => P z.1 z.2) :=
    hV.comp (contDiff_fst.prodMk
      (hVi.comp (hs.prodMk (hQ.comp (hs.prodMk
        (hU.comp (hs.prodMk hUi)))))))
  have hUif (t : Real) (x : E2) (hx : x ∉ K) : (U t).symm x = x := by
    apply (U t).injective
    change U t ((U t).symm x) = U t x
    rw [Diffeomorph.apply_symm_apply, hUfix t x hx]
  have hVif (t : Real) (x : E2) (hx : x ∉ K) : (V t).symm x = x := by
    apply (V t).injective
    change V t ((V t).symm x) = V t x
    rw [Diffeomorph.apply_symm_apply, hVfix t x hx]
  have hcancel (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (S : Set E2) :
      D.symm '' (D '' S) = S := D.toEquiv.symm_image_image S
  refine ⟨P, hPs, contDiff_planar_family_symm P hPs, ⟨K, hK, ?_⟩, ?_, ?_⟩
  · intro t x hx
    change V t ((V (σ t)).symm (Q (σ t) (U (σ t) ((U t).symm x)))) = x
    rw [hUif t x hx, hUfix (σ t) x hx, hQfix (σ t) x hx,
      hVif (σ t) x hx, hVfix t x hx]
  · intro i t ht
    have hsIJ := hσIJ t ht
    simp only [P, Diffeomorph.coe_trans, image_comp]
    rw [← hUA i t ht, hcancel,
      hUA i (σ t) hsIJ.1, hmatch i (σ t) hsIJ.2,
      ← hVB i (σ t) hsIJ.1, hcancel, hVB i t ht]
  · intro t ht x
    change V t ((V (σ t)).symm (Q (σ t) (U (σ t) ((U t).symm x)))) = Q t x
    rw [ht, Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply]

theorem exists_parametric_matching_extension_along_regular_transports
    {ι : Type*} (A B : ι → Real → Set E2) (A₀ B₀ : ι → Set E2)
    (U V : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (Q : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hU : ContDiff Real ∞ (fun z : P2 => U z.1 z.2))
    (hV : ContDiff Real ∞ (fun z : P2 => V z.1 z.2))
    (hQ : ContDiff Real ∞ (fun z : Real × Real × E2 => Q z.1 z.2.1 z.2.2))
    (hQinv : ContDiff Real ∞ (fun z : Real × Real × E2 => (Q z.1 z.2.1).symm z.2.2))
    (hzero : ∀ t x, Q 0 t x = x)
    {K : Set E2} (hK : IsCompact K)
    (hUfix : ∀ t x, x ∉ K → U t x = x)
    (hVfix : ∀ t x, x ∉ K → V t x = x)
    (hQfix : ∀ u t x, x ∉ K → Q u t x = x)
    (I J : Set Real)
    (hUA : ∀ i t, t ∈ I → U t '' A₀ i = A i t)
    (hVB : ∀ i t, t ∈ I → V t '' B₀ i = B i t)
    (hmatch : ∀ i t, t ∈ J → Q 1 t '' A i t = B i t)
    (σ : Real → Real) (hσ : ContDiff Real ∞ σ)
    (hσIJ : ∀ t ∈ I, σ t ∈ I ∩ J) :
    ∃ P : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : Real × Real × E2 => P z.1 z.2.1 z.2.2) ∧
      ContDiff Real ∞ (fun z : Real × Real × E2 => (P z.1 z.2.1).symm z.2.2) ∧
      (∀ t x, P 0 t x = x) ∧
      (∃ C : Set E2, IsCompact C ∧ ∀ u t x, x ∉ C → P u t x = x) ∧
      (∀ i t, t ∈ I → P 1 t '' A i t = B i t) ∧
      ∀ t, σ t = t → ∀ u x, P u t x = Q u t x := by
  let τ (u t : Real) := t + u * (σ t - t)
  let P (u t : Real) :=
    ((((U t).symm.trans (U (τ u t))).trans (Q u (τ u t))).trans
      (V (τ u t)).symm).trans (V t)
  have hUi := contDiff_planar_family_symm U hU
  have hVi := contDiff_planar_family_symm V hV
  have ht : ContDiff Real ∞ (fun z : Real × Real × E2 => z.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hx : ContDiff Real ∞ (fun z : Real × Real × E2 => z.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hτ : ContDiff Real ∞ (fun z : Real × Real × E2 => τ z.1 z.2.1) :=
    ht.add (contDiff_fst.mul ((hσ.comp ht).sub ht))
  have hPs : ContDiff Real ∞ (fun z : Real × Real × E2 => P z.1 z.2.1 z.2.2) :=
    hV.comp (ht.prodMk (hVi.comp (hτ.prodMk
      (hQ.comp (contDiff_fst.prodMk (hτ.prodMk
        (hU.comp (hτ.prodMk (hUi.comp (ht.prodMk hx))))))))))
  have hPis : ContDiff Real ∞
      (fun z : Real × Real × E2 => (P z.1 z.2.1).symm z.2.2) :=
    hU.comp (ht.prodMk (hUi.comp (hτ.prodMk
      (hQinv.comp (contDiff_fst.prodMk (hτ.prodMk
        (hV.comp (hτ.prodMk (hVi.comp (ht.prodMk hx))))))))))
  have hUif (t : Real) (x : E2) (hx : x ∉ K) : (U t).symm x = x := by
    apply (U t).injective
    change U t ((U t).symm x) = U t x
    rw [Diffeomorph.apply_symm_apply, hUfix t x hx]
  have hVif (t : Real) (x : E2) (hx : x ∉ K) : (V t).symm x = x := by
    apply (V t).injective
    change V t ((V t).symm x) = V t x
    rw [Diffeomorph.apply_symm_apply, hVfix t x hx]
  refine ⟨P, hPs, hPis, ?_, ⟨K, hK, ?_⟩, ?_, ?_⟩
  · intro t x
    change V t ((V (τ 0 t)).symm (Q 0 (τ 0 t) (U (τ 0 t) ((U t).symm x)))) = x
    simp only [τ, zero_mul, add_zero, hzero, Diffeomorph.apply_symm_apply]
  · intro u t x hx
    change V t ((V (τ u t)).symm (Q u (τ u t) (U (τ u t) ((U t).symm x)))) = x
    rw [hUif t x hx, hUfix _ x hx, hQfix _ _ x hx, hVif _ x hx, hVfix t x hx]
  · intro i t ht
    have hsIJ := hσIJ t ht
    have hτone : τ 1 t = σ t := by dsimp [τ]; ring
    have hcancel (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (S : Set E2) :
        D.symm '' (D '' S) = S := D.toEquiv.symm_image_image S
    simp only [P, Diffeomorph.coe_trans, image_comp, hτone]
    rw [← hUA i t ht, hcancel, hUA i (σ t) hsIJ.1,
      hmatch i (σ t) hsIJ.2, ← hVB i (σ t) hsIJ.1, hcancel, hVB i t ht]
  · intro t ht u x
    have hτeq : τ u t = t := by simp only [τ, ht, sub_self, mul_zero, add_zero]
    change V t ((V (τ u t)).symm (Q u (τ u t) (U (τ u t) ((U t).symm x)))) = Q u t x
    rw [hτeq, Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply]

theorem exists_compact_regular_band_matching
    {ι : Type*} (A B : ι → Real → Set E2) (A₀ B₀ : ι → Set E2)
    (U V : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (Q : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hU : ContDiff Real ∞ (fun z : P2 => U z.1 z.2))
    (hV : ContDiff Real ∞ (fun z : P2 => V z.1 z.2))
    (hQ : ContDiff Real ∞ (fun z : Real × Real × E2 => Q z.1 z.2.1 z.2.2))
    (hQinv : ContDiff Real ∞ (fun z : Real × Real × E2 => (Q z.1 z.2.1).symm z.2.2))
    (hzero : ∀ t x, Q 0 t x = x)
    {K : Set E2} (hK : IsCompact K)
    (hUfix : ∀ t x, x ∉ K → U t x = x)
    (hVfix : ∀ t x, x ∉ K → V t x = x)
    (hQfix : ∀ u t x, x ∉ K → Q u t x = x)
    {a b : Real} (J : Set Real)
    (hUA : ∀ i t, t ∈ Icc a b → U t '' A₀ i = A i t)
    (hVB : ∀ i t, t ∈ Icc a b → V t '' B₀ i = B i t)
    (hmatch : ∀ i t, t ∈ J → Q 1 t '' A i t = B i t)
    (σ : Real → Real) (hσ : ContDiff Real ∞ σ)
    (hσIJ : ∀ t ∈ Icc a b, σ t ∈ Icc a b ∩ J)
    {ε : Real} (hε : 0 < ε) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, (H y) 2 = y 2) ∧
      (∀ i, H '' (⋃ t ∈ Icc a b, Saddle.slice (A i t) t) =
        ⋃ t ∈ Icc a b, Saddle.slice (B i t) t) ∧
      (∀ y, y 2 ∈ Icc a b → σ (y 2) = y 2 →
        H y = Saddle.toE3 (Q 1 (y 2) (Saddle.toE2 y)) (y 2)) ∧
      (∀ y, y 2 ≤ a - ε ∨ b + ε ≤ y 2 → H y = y) ∧
      HasCompactSupport (fun y => H y - y) ∧
      HasCompactSupport (fun y => H.symm y - y) := by
  obtain ⟨P, hP, hPi, hPzero, ⟨C, hC, hPfix⟩, hPm, hPQ⟩ :=
    exists_parametric_matching_extension_along_regular_transports A B A₀ B₀ U V Q
      hU hV hQ hQinv hzero hK hUfix hVfix hQfix (Icc a b) J hUA hVB hmatch σ hσ hσIJ
  obtain ⟨H, hh, hH, _, _, hband, _, htail, hsupport, hisupport⟩ :=
    Saddle.exists_interval_supported_height_lift P isOpen_univ (subset_univ _)
      hP.contDiffOn hPi.contDiffOn (fun t _ => hPzero t) hC
      (fun u _ t _ x hx => hPfix u t x hx) hε
  refine ⟨H, hh, ?_, ?_, htail, hsupport, hisupport⟩
  · intro i
    rw [hband]
    apply iUnion_congr
    intro t
    apply iUnion_congr
    intro ht
    rw [hPm i t ht]
  · intro y hy hσy
    rw [hH y hy, hPQ (y 2) hσy]

theorem exists_matching_extension_of_regular_circle_pairs
    {a b : Real} (hab : a ≤ b)
    (c d : Fin 2 → Real → sphere (0 : E2) 1 → E2)
    (hc : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × sphere (0 : E2) 1 => c i z.1 z.2))
    (hd : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × sphere (0 : E2) 1 => d i z.1 z.2))
    (hemb : ∀ i t, t ∈ Icc a b →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i t))
    (hemb' : ∀ i t, t ∈ Icc a b →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (d i t))
    (hdisj : ∀ t ∈ Icc a b, Disjoint (range (c 0 t)) (range (c 1 t)))
    (hdisj' : ∀ t ∈ Icc a b, Disjoint (range (d 0 t)) (range (d 1 t)))
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQ : ContDiff Real ∞ (fun z : P2 => Q z.1 z.2))
    {K : Set E2} (hK : IsCompact K)
    (hQfix : ∀ t x, x ∉ K → Q t x = x)
    (J : Set Real)
    (hmatch : ∀ i t, t ∈ J → Q t '' range (c i t) = range (d i t))
    (σ : Real → Real) (hσ : ContDiff Real ∞ σ)
    (hσIJ : ∀ t ∈ Icc a b, σ t ∈ Icc a b ∩ J) :
    ∃ P : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : P2 => P z.1 z.2) ∧
      ContDiff Real ∞ (fun z : P2 => (P z.1).symm z.2) ∧
      (∃ C : Set E2, IsCompact C ∧ ∀ t x, x ∉ C → P t x = x) ∧
      (∀ i t, t ∈ Icc a b → P t '' range (c i t) = range (d i t)) ∧
      ∀ t, σ t = t → ∀ x, P t x = Q t x := by
  obtain ⟨KU, hKU, U, _, hU, _, hUfix, hUm⟩ :=
    Plane.Isotopy.ArcPairs.exists_planar_circle_pair_family_extension hab c hc hemb hdisj
  obtain ⟨KV, hKV, V, _, hV, _, hVfix, hVm⟩ :=
    Plane.Isotopy.ArcPairs.exists_planar_circle_pair_family_extension hab d hd hemb' hdisj'
  apply exists_matching_extension_along_regular_transports
    (fun i t => range (c i t)) (fun i t => range (d i t))
    (fun i => range (c i a)) (fun i => range (d i a)) U V Q hU hV hQ
    ((hKU.union hKV).union hK)
    (fun t x hx => hUfix t x (fun h => hx (Or.inl (Or.inl h))))
    (fun t x hx => hVfix t x (fun h => hx (Or.inl (Or.inr h))))
    (fun t x hx => hQfix t x (fun h => hx (Or.inr h))) (Icc a b) J
    ?_ ?_ hmatch σ hσ hσIJ
  · intro i t ht
    rw [← range_comp]
    exact congrArg range (funext (hUm i t ht))
  · intro i t ht
    rw [← range_comp]
    exact congrArg range (funext (hVm i t ht))

theorem exists_relative_matching_of_two_physical_height_strips
    {g₀ g₁ : S2 → E3}
    (hg₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g₀)
    (hg₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g₁)
    {v : E3} (hv : ‖v‖ = 1) (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2)
    (F₀ F₁ : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (l l₀ l₁ u₁ u₀ u : Fin 2 → Real) {w c r R : Real}
    (hr : 0 < r) (hrw : r < w) (hrR : r < R)
    (hll₀ : ∀ i, l i ≤ l₀ i) (hl₀l₁ : ∀ i, l₀ i < l₁ i)
    (hl₁u₁ : ∀ i, l₁ i ≤ u₁ i) (hu₁u₀ : ∀ i, u₁ i < u₀ i)
    (hu₀u : ∀ i, u₀ i ≤ u i)
    (hs₀ : ∀ i, (F₀ i).source = Ioo (l i - w) (u i + w) ×ˢ Ioo (-w) w)
    (hs₁ : ∀ i, (F₁ i).source = Ioo (l i - w) (u i + w) ×ˢ Ioo (-w) w)
    (hF₀ : ∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F₀ i) (F₀ i).source)
    (hFi₀ : ∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F₀ i).symm (F₀ i).target)
    (hF₁ : ∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F₁ i) (F₁ i).source)
    (hFi₁ : ∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F₁ i).symm (F₁ i).target)
    (hh₀ : ∀ i z, z ∈ (F₀ i).source → inner Real v (g₀ (F₀ i z)) = c + z.2)
    (hh₁ : ∀ i z, z ∈ (F₁ i).source → inner Real v (g₁ (F₁ i z)) = c + z.2)
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hcentral : ∀ i s, s ∈ Icc (l i) (u i) →
      Q (stripPlaneMap g₀ v J (F₀ i) (s, 0)) = stripPlaneMap g₁ v J (F₁ i) (s, 0))
    (hends : ∀ i t, t ∈ Icc (-r) r → ∀ s ∈ Icc (l i) (l₁ i) ∪ Icc (u₁ i) (u i),
      Q (stripPlaneMap g₀ v J (F₀ i) (s, t)) = stripPlaneMap g₁ v J (F₁ i) (s, t))
    (U : Fin 2 → Set E2) (hU : ∀ i, IsOpen (U i))
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hproject₀ : ∀ i q, q ∈ (F₀ i).target →
      Q (J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g₀ q))) ∈ U i)
    (hproject₁ : ∀ i q, q ∈ (F₁ i).target →
      J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g₁ q)) ∈ U i) :
    ∃ (K : Set E2) (V : Set P2), IsCompact K ∧ K ⊆ U 0 ∪ U 1 ∧ IsOpen V ∧
      (∀ i t, t ∈ Icc (-r) r → ∀ s ∈ Icc (l i) (l₀ i) ∪ Icc (u₀ i) (u i),
        (t, stripPlaneMap g₀ v J (F₀ i) (s, t)) ∈ V) ∧
      ∃ H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
        (∀ z, (H z).1 = z.1) ∧
        (∀ x, H (0, x) = (0, Q x)) ∧
        (∀ z, (z.1, Q z.2) ∉ closedBall (0 : Real) R ×ˢ K → H z = (z.1, Q z.2)) ∧
        (∀ z ∈ V, H z = (z.1, Q z.2)) ∧
        (∀ i t, t ∈ Icc (-r) r → ∀ s ∈ Icc (l i) (u i),
          H (t, stripPlaneMap g₀ v J (F₀ i) (s, t)) =
            (t, stripPlaneMap g₁ v J (F₁ i) (s, t))) ∧
        ∀ i, physicalStripConjugate hv J c H ''
            (g₀ '' (F₀ i '' (Icc (l i) (u i) ×ˢ Icc (-r) r))) =
          g₁ '' (F₁ i '' (Icc (l i) (u i) ×ˢ Icc (-r) r)) := by
  choose K V hK hKU hV hendsV H hHt hHzero hHfix hHV hHmatch hHimage using
    fun i : Fin 2 => exists_relative_matching_of_physical_height_strips
      hg₀ hg₁ hv J (F₀ i) (F₁ i) hr hrw hrR
      (hll₀ i) (hl₀l₁ i) (hl₁u₁ i) (hu₁u₀ i) (hu₀u i)
      (hs₀ i) (hs₁ i) (hF₀ i) (hFi₀ i) (hF₁ i) (hFi₁ i)
      (hh₀ i) (hh₁ i) Q (hcentral i) (hends i) (hU i) (hproject₀ i) (hproject₁ i)
  let Qlift : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞ := {
    toEquiv := (Equiv.refl Real).prodCongr Q.toEquiv
    contMDiff_toFun := (contDiff_fst.prodMk
      (Q.contMDiff.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (Q.symm.contMDiff.contDiff.comp contDiff_snd)).contMDiff }
  let D (i : Fin 2) := Qlift.symm.trans (H i)
  let O (i : Fin 2) : Set P2 := Prod.snd ⁻¹' U i
  let C (i : Fin 2) := closedBall (0 : Real) R ×ˢ K i
  have hC (i : Fin 2) : IsCompact (C i) := (isCompact_closedBall 0 R).prod (hK i)
  have hCO (i : Fin 2) : C i ⊆ O i := fun z hz => hKU i hz.2
  have hOdisjoint : Pairwise (fun i j => Disjoint (O i) (O j)) :=
    fun i j hij => (hdisjoint hij).preimage Prod.snd
  have hDfix (i : Fin 2) (z : P2) (hz : z ∉ C i) : D i z = z := by
    change H i (z.1, Q.symm z.2) = z
    have hnot : (z.1, Q (Q.symm z.2)) ∉ C i := by simpa using hz
    simpa using hHfix i (z.1, Q.symm z.2) hnot
  have hDt (i : Fin 2) (z : P2) : (D i z).1 = z.1 := hHt i (Qlift.symm z)
  have hDzero (i : Fin 2) (x : E2) : D i (0, x) = (0, x) := by
    change H i (0, Q.symm x) = (0, x)
    rw [hHzero, Q.apply_symm_apply]
  obtain ⟨_, _, hfix, hagree⟩ :=
    Diffeomorph.trans_compact_support_fin_two D C O hC hCO hOdisjoint hDfix
  let A := Qlift.trans ((D 0).trans (D 1))
  have hA (i : Fin 2) (z : P2) (hz : Q z.2 ∈ U i) : A z = H i z := by
    have heq := hagree i (x := Qlift z) hz
    change D 1 (D 0 (Qlift z)) = H i (Qlift.symm (Qlift z)) at heq
    change D 1 (D 0 (Qlift z)) = H i z
    simpa only [Diffeomorph.symm_apply_apply] using heq
  let W : Set P2 := ⋃ i, V i ∩ Qlift ⁻¹' O i
  have hsource₀ (i : Fin 2) (t s : Real) (ht : t ∈ Icc (-r) r)
      (hs : s ∈ Icc (l i) (u i)) : (s, t) ∈ (F₀ i).source := by
    rw [hs₀ i]
    have hw := hr.trans hrw
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have htrace (i : Fin 2) (t s : Real) (ht : t ∈ Icc (-r) r)
      (hs : s ∈ Icc (l i) (u i)) :
      Q (stripPlaneMap g₀ v J (F₀ i) (s, t)) ∈ U i :=
    hproject₀ i _ ((F₀ i).map_source (hsource₀ i t s ht hs))
  have hmatch (i : Fin 2) (t : Real) (ht : t ∈ Icc (-r) r)
      (s : Real) (hs : s ∈ Icc (l i) (u i)) :
      A (t, stripPlaneMap g₀ v J (F₀ i) (s, t)) =
        (t, stripPlaneMap g₁ v J (F₁ i) (s, t)) :=
    (hA i _ (htrace i t s ht hs)).trans (hHmatch i t ht s hs)
  refine ⟨K 0 ∪ K 1, W, (hK 0).union (hK 1), union_subset_union (hKU 0) (hKU 1),
    isOpen_iUnion (fun i => (hV i).inter
      (((hU i).preimage continuous_snd).preimage Qlift.contMDiff.continuous)),
    ?_, A, ?_, ?_, ?_, ?_, hmatch, ?_⟩
  · intro i t ht s hs
    have hsu : s ∈ Icc (l i) (u i) := by
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans ((hl₀l₁ i).le.trans
          ((hl₁u₁ i).trans ((hu₁u₀ i).le.trans (hu₀u i))))⟩
      · exact ⟨((hll₀ i).trans ((hl₀l₁ i).le.trans
          ((hl₁u₁ i).trans (hu₁u₀ i).le))).trans hs.1, hs.2⟩
    exact mem_iUnion.mpr ⟨i, hendsV i t ht s hs, htrace i t s ht hsu⟩
  · intro z
    exact (hDt 1 _).trans (hDt 0 _)
  · intro x
    change D 1 (D 0 (0, Q x)) = (0, Q x)
    rw [hDzero, hDzero]
  · intro z hz
    apply hfix (Qlift z)
    rintro (h0 | h1)
    · exact hz ⟨h0.1, Or.inl h0.2⟩
    · exact hz ⟨h1.1, Or.inr h1.2⟩
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion.mp hz
    exact (hA i z hzi).trans (hHV i z hi)
  · intro i
    apply physicalStripConjugate_image_strip hv J c A g₀ g₁ (F₀ i) (F₁ i)
    · intro z hz
      exact hh₀ i z (hsource₀ i z.2 z.1 hz.2 hz.1)
    · intro z hz
      apply hh₁ i z
      rw [hs₁ i]
      have hw := hr.trans hrw
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
        ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
    · intro z hz
      exact hmatch i z.2 hz.2 z.1 hz.1

theorem exists_compact_localization_of_relative_matching
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun z : P2 => Φ z.1 z.2))
    (hzero : ∀ x, Φ 0 x = x)
    {KΦ K : Set E2} (hKΦ : IsCompact KΦ) (hK : IsCompact K)
    (hΦfix : ∀ t x, x ∉ KΦ → Φ t x = x)
    {r R : Real} (hr : 0 < r) (hrR : r < R)
    (H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞)
    (hHt : ∀ z, (H z).1 = z.1)
    (hHfix : ∀ z, (z.1, Φ 1 z.2) ∉ closedBall (0 : Real) R ×ˢ K →
      H z = (z.1, Φ 1 z.2)) :
    ∃ A : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
      (∀ z, (A z).1 = z.1) ∧
      (∀ z, z.1 ∈ closedBall (0 : Real) r → A z = H z) ∧
      IsCompact (closedBall (0 : Real) R ×ˢ (K ∪ KΦ)) ∧
      ∀ z, z ∉ closedBall (0 : Real) R ×ˢ (K ∪ KΦ) → A z = z := by
  let Q := Φ 1
  let Qlift : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞ := {
    toEquiv := (Equiv.refl Real).prodCongr Q.toEquiv
    contMDiff_toFun := (contDiff_fst.prodMk
      (Q.contMDiff.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (Q.symm.contMDiff.contDiff.comp contDiff_snd)).contMDiff }
  let D := Qlift.symm.trans H
  have hDfix (z : P2) (hz : z ∉ closedBall (0 : Real) R ×ˢ K) : D z = z := by
    change H (z.1, Q.symm z.2) = z
    have hnot : (z.1, Φ 1 (Q.symm z.2)) ∉ closedBall (0 : Real) R ×ˢ K := by
      simpa only [← show Q = Φ 1 from rfl, Diffeomorph.apply_symm_apply] using hz
    simpa only [← show Q = Φ 1 from rfl, Diffeomorph.apply_symm_apply,
      Prod.mk.eta] using hHfix (z.1, Q.symm z.2) hnot
  have hDt (z : P2) : (D z).1 = z.1 := hHt (Qlift.symm z)
  let χ : ContDiffBump (0 : Real) := ⟨r, R, hr, hrR⟩
  have hΦm : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : P2 => Φ z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hΦ.contMDiff
  have hΦinv := Poincare.Manifold.contMDiff_diffeomorph_family_symm Φ hΦm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hΦinv
  obtain ⟨L, hL, _⟩ :=
    Saddle.exists_height_cutoff_lift_product Φ hΦ hΦinv.contDiff χ χ.contDiff
  let A := L.trans D
  refine ⟨A, ?_, ?_, (isCompact_closedBall 0 R).prod (hK.union hKΦ), ?_⟩
  · intro z
    change (D (L z)).1 = z.1
    rw [hDt, hL]
  · intro z hz
    change D (L z) = H z
    rw [hL, χ.one_of_mem_closedBall hz]
    change H (z.1, Q.symm (Q z.2)) = H z
    rw [Diffeomorph.symm_apply_apply, Prod.mk.eta]
  · intro z hz
    have hLK : L z = z := by
      rw [hL]
      by_cases ht : z.1 ∈ closedBall (0 : Real) R
      · rw [hΦfix _ _ (fun hx => hz ⟨ht, Or.inr hx⟩)]
      · rw [χ.zero_of_le_dist (le_of_lt (not_le.mp ht)), hzero]
    change D (L z) = z
    rw [hLK]
    exact hDfix z (fun hzK => hz ⟨hzK.1, Or.inl hzK.2⟩)

theorem physicalStripConjugate_eq_self_outside_slab
    {v : E3} (hv : ‖v‖ = 1) (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (c R : Real)
    (H : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞)
    {K : Set E2}
    (hfix : ∀ z, z ∉ closedBall (0 : Real) R ×ˢ K → H z = z)
    {x : E3} (hx : R < |inner Real v x - c|) :
    physicalStripConjugate hv J c H x = x := by
  have hnot : (physicalStripHeightCoordinates hv J c).symm x ∉
      closedBall (0 : Real) R ×ˢ K := by
    intro h
    have ht := h.1
    rw [physicalStripHeightCoordinates_symm] at ht
    exact (not_le.mpr hx) (by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht)
  change physicalStripHeightCoordinates hv J c
    (H ((physicalStripHeightCoordinates hv J c).symm x)) = x
  rw [hfix _ hnot, Diffeomorph.apply_symm_apply]

theorem image_slice_family_of_planar_transport
     (H₀ : E3 → E3) (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
     (χ : Real → Real) (I : Set Real) (A B : Real → Set E2)
     (hSlice : ∀ (S : Set E2) (c : Real),
       H₀ '' Saddle.Levels.slice S c =
         Saddle.Levels.slice (Φ (χ c) '' S) c)
     (hPlanar : ∀ c : Real, Φ (χ c) '' A c = B c) :
     H₀ '' (⋃ c ∈ I, Saddle.Levels.slice (A c) c) =
       ⋃ c ∈ I, Saddle.Levels.slice (B c) c := by
   rw [image_iUnion]
   apply iUnion_congr
   intro c
   rw [image_iUnion]
   apply iUnion_congr
   intro hc
   rw [hSlice, hPlanar]

theorem saddle_slice_eq_levels_slice (S : Set E2) (c : Real) :
     Saddle.slice S c = Saddle.Levels.slice S c := by
   rfl

theorem image_slice_family_of_height_cutoff_lift
     (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
     (χ : Real → Real) (I : Set Real) (A B : Real → Set E2)
     (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
     (hH : ∀ (S : Set E2) (c : Real), H '' Saddle.slice S c =
       Saddle.slice (Φ (χ c) '' S) c)
     (hPlanar : ∀ c : Real, Φ (χ c) '' A c = B c) :
     H '' (⋃ c ∈ I, Saddle.Levels.slice (A c) c) =
       ⋃ c ∈ I, Saddle.Levels.slice (B c) c := by
   apply image_slice_family_of_planar_transport H Φ χ I A B
   · intro S c
     rw [← saddle_slice_eq_levels_slice S c,
       ← saddle_slice_eq_levels_slice (Φ (χ c) '' S) c]
     exact hH S c
   · exact hPlanar

theorem exists_global_saddle_matching_of_slice_interfaces
     {g : S2 → E3}
     (Ψ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
     (H₀ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
     (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
     (χ : Real → Real) (I : Set Real) (A B : Real → Set E2)
     (C₀ C₁ M₀ M₁ model : Set E3)
     (hActual : Ψ '' range g =
       (⋃ c ∈ I, Saddle.Levels.slice (A c) c) ∪ C₀ ∪ C₁)
     (hSlice : ∀ (S : Set E2) (c : Real),
       H₀ '' Saddle.Levels.slice S c =
         Saddle.Levels.slice (Φ (χ c) '' S) c)
     (hPlanar : ∀ c : Real, Φ (χ c) '' A c = B c)
     (hCap₀ : H₀ '' C₀ = M₀) (hCap₁ : H₀ '' C₁ = M₁)
     (hModel : (⋃ c ∈ I, Saddle.Levels.slice (B c) c) ∪ M₀ ∪ M₁ = model) :
     ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞, H '' range g = model := by
   have hBand : H₀ '' (⋃ c ∈ I, Saddle.Levels.slice (A c) c) =
       ⋃ c ∈ I, Saddle.Levels.slice (B c) c :=
     image_slice_family_of_planar_transport H₀ Φ χ I A B hSlice hPlanar
   refine ⟨Ψ.trans H₀, ?_⟩
   rw [Diffeomorph.coe_trans, image_comp, hActual, image_union, image_union,
     hBand, hCap₀, hCap₁, hModel]

theorem exists_global_saddle_matching_of_height_cutoff_interfaces
     {g : S2 → E3}
     (Ψ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
     (H₀ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
     (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
     (χ : Real → Real) (I : Set Real) (A B : Real → Set E2)
     (C₀ C₁ M₀ M₁ model : Set E3)
     (hActual : Ψ '' range g =
       (⋃ c ∈ I, Saddle.Levels.slice (A c) c) ∪ C₀ ∪ C₁)
     (hLift : ∀ (S : Set E2) (c : Real), H₀ '' Saddle.slice S c =
       Saddle.slice (Φ (χ c) '' S) c)
     (hPlanar : ∀ c : Real, Φ (χ c) '' A c = B c)
     (hCap₀ : H₀ '' C₀ = M₀) (hCap₁ : H₀ '' C₁ = M₁)
     (hModel : (⋃ c ∈ I, Saddle.Levels.slice (B c) c) ∪ M₀ ∪ M₁ = model) :
     ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞, H '' range g = model := by
   apply exists_global_saddle_matching_of_slice_interfaces Ψ H₀ Φ χ I A B
     C₀ C₁ M₀ M₁ model hActual
   · intro S c
     rw [← saddle_slice_eq_levels_slice S c,
       ← saddle_slice_eq_levels_slice (Φ (χ c) '' S) c]
     exact hLift S c
   · exact hPlanar
   · exact hCap₀
   · exact hCap₁
   · exact hModel

private theorem exists_lift_matching_circle_families
    {ι : Type*} (c d : ι → Real → sphere (0 : E2) 1 → E2)
    (q : ι → Diffeomorph (𝓡 1) (𝓡 1) (sphere (0 : E2) 1) (sphere (0 : E2) 1) ∞)
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun z : P2 => Φ z.1 z.2))
    (hΦinv : ContDiff Real ∞ (fun z : P2 => (Φ z.1).symm z.2))
    {K : Set E2} (hfix : ∀ t x, x ∉ K → Φ t x = x)
    {I : Set Real} (hm : ∀ t ∈ I, ∀ i p, Φ t (c i t p) = d i t (q i p)) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, (H y) 2 = y 2) ∧
      (∀ y, Saddle.toE2 y ∉ K → H y = y) ∧
      (∀ t ∈ I, ∀ i p,
        H (Saddle.toE3 (c i t p) t) = Saddle.toE3 (d i t (q i p)) t) ∧
      ∀ i, H '' (⋃ t ∈ I, Saddle.slice (range (c i t)) t) =
        ⋃ t ∈ I, Saddle.slice (range (d i t)) t := by
  obtain ⟨H, hH, _, hh, hs⟩ := Saddle.exists_height_lift Φ hΦ hΦinv
  have hcoord (x : E2) (t : Real) : Saddle.toE2 (Saddle.toE3 x t) = x := by
    ext i
    fin_cases i <;> rfl
  have hcoord' (y : E3) : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  have himage (i : ι) (t : Real) (ht : t ∈ I) :
      Φ t '' range (c i t) = range (d i t) := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨q i p, (hm t ht i p).symm⟩
    · rintro ⟨p, rfl⟩
      refine ⟨c i t ((q i).symm p), mem_range_self _, ?_⟩
      rw [hm t ht i, Diffeomorph.apply_symm_apply]
  refine ⟨H, hh, ?_, ?_, ?_⟩
  · intro y hy
    rw [hH, hfix _ _ hy, hcoord']
  · intro t ht i p
    rw [hH, hcoord]
    exact congrArg (fun x => Saddle.toE3 x t) (hm t ht i p)
  · intro i
    simp only [image_iUnion]
    apply iUnion_congr
    intro t
    apply iUnion_congr
    intro ht
    rw [hs, himage i t ht]

theorem exists_regular_circle_band_matching
    {a b : Real} (hab : a < b)
    (c d : Real → sphere (0 : E2) 1 → E2)
    (hc : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × sphere (0 : E2) 1 => c z.1 z.2))
    (hd : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × sphere (0 : E2) 1 => d z.1 z.2))
    (hemb : ∀ t ∈ Icc a b,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c t))
    (hemb' : ∀ t ∈ Icc a b,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (d t)) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) (sphere (0 : E2) 1) (sphere (0 : E2) 1) ∞,
      ∃ K : Set E2, IsCompact K ∧
        ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y, (H y) 2 = y 2) ∧
          (∀ y, Saddle.toE2 y ∉ K → H y = y) ∧
          (∀ t ∈ Icc a b, ∀ p,
            H (Saddle.toE3 (c t p) t) = Saddle.toE3 (d t (q p)) t) ∧
          H '' (⋃ t ∈ Icc a b, Saddle.slice (range (c t)) t) =
            ⋃ t ∈ Icc a b, Saddle.slice (range (d t)) t := by
  obtain ⟨q, K, hK, Φ, hΦ, hΦinv, hfix, hm⟩ :=
    Plane.Isotopy.ArcPairs.exists_planar_circle_family_isotopy hab c d hc hd hemb hemb'
  obtain ⟨H, hh, hHfix, hHpoint, hHband⟩ :=
    exists_lift_matching_circle_families (fun _ : Unit => c) (fun _ : Unit => d)
      (fun _ => q) Φ hΦ hΦinv hfix (fun t ht _ => hm t ht)
  exact ⟨q, K, hK, H, hh, hHfix, fun t ht => hHpoint t ht (), hHband ()⟩

theorem exists_regular_circle_pair_band_matching
    {a b : Real} (hab : a < b)
    (c d : Fin 2 → Real → sphere (0 : E2) 1 → E2)
    (hc : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × sphere (0 : E2) 1 => c i z.1 z.2))
    (hd : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × sphere (0 : E2) 1 => d i z.1 z.2))
    (hemb : ∀ i t, t ∈ Icc a b →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i t))
    (hemb' : ∀ i t, t ∈ Icc a b →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (d i t))
    (hdisj : ∀ t ∈ Icc a b, Disjoint (range (c 0 t)) (range (c 1 t)))
    (hdisj' : ∀ t ∈ Icc a b, Disjoint (range (d 0 t)) (range (d 1 t)))
    (hnest : ∀ t ∈ Icc a b, ∀ i j, i ≠ j →
      (Plane.Isotopy.ArcPairs.NestedPair (c i t) (c j t) ↔
        Plane.Isotopy.ArcPairs.NestedPair (d i t) (d j t))) :
    ∃ q : Fin 2 → Diffeomorph (𝓡 1) (𝓡 1)
        (sphere (0 : E2) 1) (sphere (0 : E2) 1) ∞,
      ∃ K : Set E2, IsCompact K ∧
        ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y, (H y) 2 = y 2) ∧
          (∀ y, Saddle.toE2 y ∉ K → H y = y) ∧
          (∀ t ∈ Icc a b, ∀ i p,
            H (Saddle.toE3 (c i t p) t) = Saddle.toE3 (d i t (q i p)) t) ∧
          ∀ i, H '' (⋃ t ∈ Icc a b, Saddle.slice (range (c i t)) t) =
            ⋃ t ∈ Icc a b, Saddle.slice (range (d i t)) t := by
  obtain ⟨q, K, hK, Φ, hΦ, hΦinv, hfix, hm⟩ :=
    Plane.Isotopy.ArcPairs.exists_planar_circle_pair_family_isotopy
      hab c d hc hd hemb hemb' hdisj hdisj' hnest
  exact ⟨q, K, hK, exists_lift_matching_circle_families c d q Φ hΦ hΦinv hfix hm⟩

theorem exists_simultaneous_three_cap_replacement
    (band : Set E3) (E M : Fin 3 → Set E3)
    (hreplace : ∀ i, ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      EqOn G id band ∧ G '' E i = M i ∧
      (∀ j, i < j → EqOn G id (E j)) ∧
      ∀ j, j < i → EqOn G id (M j)) :
    ∃ H₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      EqOn H₂ id band ∧ ∀ i, H₂ '' E i = M i := by
  classical
  choose G hband hmatch hsourcefix htargetfix using hreplace
  have hsource (i j : Fin 3) (hij : i < j) : G i '' E j = E j := by
    calc
      G i '' E j = id '' E j := image_congr (hsourcefix i j hij)
      _ = E j := image_id _
  have htarget (i j : Fin 3) (hij : j < i) : G i '' M j = M j := by
    calc
      G i '' M j = id '' M j := image_congr (htargetfix i j hij)
      _ = M j := image_id _
  refine ⟨((G 0).trans (G 1)).trans (G 2), ?_, ?_⟩
  · intro x hx
    change G 2 (G 1 (G 0 x)) = x
    rw [hband 0 hx, id_eq, hband 1 hx, id_eq, hband 2 hx, id_eq]
  · intro i
    simp only [Diffeomorph.coe_trans, image_comp]
    fin_cases i
    · change G 2 '' (G 1 '' (G 0 '' E 0)) = M 0
      rw [hmatch 0, htarget 1 0 (by decide), htarget 2 0 (by decide)]
    · change G 2 '' (G 1 '' (G 0 '' E 1)) = M 1
      rw [hsource 0 1 (by decide), hmatch 1, htarget 2 1 (by decide)]
    · change G 2 '' (G 1 '' (G 0 '' E 2)) = M 2
      rw [hsource 0 2 (by decide), hsource 1 2 (by decide), hmatch 2]

theorem exists_global_saddle_matching_of_interfaces
    {g : S2 → E3}
    (H₁ H₂ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (band modelBand : Set E3) (C M : Fin 3 → Set E3)
    (hdecomp : range g = band ∪ ⋃ i, C i)
    (hband : H₁ '' band = modelBand)
    (hfix : EqOn H₂ id modelBand)
    (hcaps : ∀ i, H₂ '' (H₁ '' C i) = M i)
    (hmodel : F '' sphere (0 : E3) 1 = modelBand ∪ ⋃ i, M i) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      H '' range g = Saddle.shear '' sphere (0 : E3) 1 ∧
      ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : E3) 1 = range g := by
  have hbandfix : H₂ '' modelBand = modelBand := by
    calc
      H₂ '' modelBand = id '' modelBand := image_congr hfix
      _ = modelBand := image_id modelBand
  have hmatched : (H₁.trans H₂) '' range g = F '' sphere (0 : E3) 1 := by
    rw [Diffeomorph.coe_trans, image_comp, hdecomp, hmodel]
    simp only [image_union, image_iUnion, hband, hbandfix, hcaps]
  let H := (H₁.trans H₂).trans (F.symm.trans Saddle.shear)
  have hH : H '' range g = Saddle.shear '' sphere (0 : E3) 1 := by
    change ((H₁.trans H₂).trans (F.symm.trans Saddle.shear)) '' range g = _
    rw [Diffeomorph.coe_trans, image_comp, hmatched, Diffeomorph.coe_trans, image_comp]
    have hcancel : F.symm '' (F '' sphere (0 : E3) 1) = sphere (0 : E3) 1 :=
      F.toEquiv.symm_image_image _
    rw [hcancel]
  exact ⟨H, hH, Saddle.exists_ambient_ball_of_global_saddle_matching H hH⟩

theorem exists_global_saddle_matching_of_flattened_frame
    {g : S2 → E3}
    (D H' F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (flatRange : Set E3)
    (hflat : D '' range g = flatRange)
    (hmatch : H' '' flatRange = F '' sphere (0 : E3) 1) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      H '' range g = Saddle.shear '' sphere (0 : E3) 1 ∧
      ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : E3) 1 = range g := by
  let H := D.trans (H'.trans (F.symm.trans Saddle.shear))
  have hH : H '' range g = Saddle.shear '' sphere (0 : E3) 1 := by
    dsimp [H]
    simp only [image_comp]
    have hcancel : F.symm '' (F '' sphere (0 : E3) 1) = sphere (0 : E3) 1 :=
      F.toEquiv.symm_image_image _
    rw [hflat, hmatch, hcancel]
  let B := F.trans (H'.symm.trans D.symm)
  have hinv : H'.symm '' (F '' sphere (0 : E3) 1) = D '' range g := by
    calc
      H'.symm '' (F '' sphere (0 : E3) 1) =
          H'.symm '' (H' '' flatRange) := congrArg (fun s => H'.symm '' s) hmatch.symm
      _ = flatRange := H'.toEquiv.symm_image_image _
      _ = D '' range g := hflat.symm
  have hB : B '' sphere (0 : E3) 1 = range g := by
    dsimp [B]
    simp only [image_comp]
    rw [hinv]
    exact D.toEquiv.symm_image_image _
  exact ⟨H, hH, B, hB⟩

theorem exists_global_saddle_matching_of_flattened_three_cap_replacements
    {g : S2 → E3}
    (D H₁ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (band modelBand : Set E3) (C M : Fin 3 → Set E3)
    (hactual : D '' range g = band ∪ ⋃ i, C i)
    (hband : H₁ '' band = modelBand)
    (hmodel : D '' (F '' sphere (0 : E3) 1) = modelBand ∪ ⋃ i, M i)
    (hreplace : ∀ i, ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      EqOn G id modelBand ∧ G '' (H₁ '' C i) = M i ∧
      (∀ j, i < j → EqOn G id (H₁ '' C j)) ∧
      ∀ j, j < i → EqOn G id (M j)) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      H '' range g = F '' sphere (0 : E3) 1 ∧
      ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : E3) 1 = range g := by
  obtain ⟨H₂, hfix, hcaps⟩ := exists_simultaneous_three_cap_replacement
    modelBand (fun i => H₁ '' C i) M hreplace
  have hbandfix : H₂ '' modelBand = modelBand := by
    calc
      H₂ '' modelBand = id '' modelBand := image_congr hfix
      _ = modelBand := image_id _
  have hmatched : (H₁.trans H₂) '' (D '' range g) =
      D '' (F '' sphere (0 : E3) 1) := by
    rw [Diffeomorph.coe_trans, image_comp, hactual, hmodel]
    simp only [image_union, image_iUnion, hband, hbandfix, hcaps]
  let H := D.trans ((H₁.trans H₂).trans D.symm)
  have hH : H '' range g = F '' sphere (0 : E3) 1 := by
    change (D.trans ((H₁.trans H₂).trans D.symm)) '' range g = _
    rw [Diffeomorph.coe_trans, image_comp, Diffeomorph.coe_trans, image_comp,
      hmatched]
    exact D.toEquiv.symm_image_image _
  refine ⟨H, hH, F.trans H.symm, ?_⟩
  rw [Diffeomorph.coe_trans, image_comp, ← hH]
  exact H.toEquiv.symm_image_image _

theorem exists_global_saddle_matching_of_band_and_three_cap_replacement
    {g : S2 → E3}
    (H₁ H₂ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (band C₀ C₁ C₂ modelBand M₀ M₁ M₂ : Set E3)
    (hdecomp : range g = band ∪ C₀ ∪ C₁ ∪ C₂)
    (hband : H₁ '' band = modelBand)
    (hfix : EqOn H₂ id modelBand)
    (hcap₀ : H₂ '' (H₁ '' C₀) = M₀)
    (hcap₁ : H₂ '' (H₁ '' C₁) = M₁)
    (hcap₂ : H₂ '' (H₁ '' C₂) = M₂)
    (hmodel : F '' sphere (0 : E3) 1 = modelBand ∪ M₀ ∪ M₁ ∪ M₂) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      H '' range g = Saddle.shear '' sphere (0 : E3) 1 ∧
      ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : E3) 1 = range g := by
  let C : Fin 3 → Set E3 := ![C₀, C₁, C₂]
  let M : Fin 3 → Set E3 := ![M₀, M₁, M₂]
  have hCunion : (⋃ i, C i) = C₀ ∪ C₁ ∪ C₂ := by
    ext x
    simp only [C, mem_iUnion, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with (hx | hx) | hx
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
      · exact ⟨2, hx⟩
  have hMunion : (⋃ i, M i) = M₀ ∪ M₁ ∪ M₂ := by
    ext x
    simp only [M, mem_iUnion, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with (hx | hx) | hx
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
      · exact ⟨2, hx⟩
  have hdecomp' : range g = band ∪ ⋃ i, C i := by
    rw [hCunion]
    simpa only [union_assoc] using hdecomp
  have hcaps : ∀ i, H₂ '' (H₁ '' C i) = M i := by
    intro i
    fin_cases i
    · exact hcap₀
    · exact hcap₁
    · exact hcap₂
  have hmodel' : F '' sphere (0 : E3) 1 = modelBand ∪ ⋃ i, M i := by
    rw [hMunion]
    simpa only [union_assoc] using hmodel
  exact exists_global_saddle_matching_of_interfaces H₁ H₂ F band modelBand C M
    hdecomp' hband hfix hcaps hmodel'

theorem exists_global_saddle_matching_of_parametric_interfaces
    {g : S2 → E3}
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    {K : Set E2} (hfix : ∀ t z x, x ∉ K → Φ t z x = x)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ)
    (I : Set Real) (A B : Real → Set E2) (C M : Fin 3 → Set E3)
    (hχone : ∀ z ∈ I, χ z = 1)
    (hplanar : ∀ z ∈ I, Φ 1 z '' A z = B z)
    (hactual : range g = (⋃ z ∈ I, Saddle.slice (A z) z) ∪ ⋃ i, C i)
    (hmodel : F '' sphere (0 : E3) 1 =
      (⋃ z ∈ I, Saddle.slice (B z) z) ∪ ⋃ i, M i)
    (hreplace : ∀ H₁ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, H₁ y = Saddle.toE3 (Φ (χ (y 2)) (y 2) (Saddle.toE2 y)) (y 2)) →
      ∃ H₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        EqOn H₂ id (⋃ z ∈ I, Saddle.slice (B z) z) ∧
        ∀ i, H₂ '' (H₁ '' C i) = M i) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      H '' range g = Saddle.shear '' sphere (0 : E3) 1 ∧
      ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : E3) 1 = range g := by
  obtain ⟨H₁, hH₁, _, _, hslice, _, _⟩ :=
    Saddle.exists_parametric_height_cutoff_lift Φ hzero hΦ hΦinv hfix χ hχ
  have hband := Saddle.image_iUnion_slice_parametric_of_matching Φ χ A B H₁
    hslice hχone hplanar
  obtain ⟨H₂, hH₂fix, hH₂caps⟩ := hreplace H₁ hH₁
  exact exists_global_saddle_matching_of_interfaces H₁ H₂ F _ _ C M
    hactual hband hH₂fix hH₂caps hmodel

end Poincare.Manifold.Schoenflies.SaddleLevel
