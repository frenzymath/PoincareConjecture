import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NativeSourceArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.ReferenceIncidence
import PoincareConjecture.Proofs.M25.Mathlib.SignedHyperbolaChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ReferencePositiveLevels

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_reference_lane_source_arcs
    (sigma : ℝ) (_hsigma : sigma = 1 ∨ sigma = -1)
    (iTar : Fin 2)
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ i : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta))
    (hqd : ∀ i l : Fin 2, i ≠ l →
      Disjoint (range (q i)) (range (q l)))
    (gamma : Fin 2 → unitInterval → UnitTwoSphere)
    (hgamma : ∀ i : Fin 2,
      Continuous (gamma i) ∧ Function.Injective (gamma i))
    (hgdisjoint : Disjoint (range (gamma 0)) (range (gamma 1)))
    (p : Fin 4 → UnitTwoSphere)
    (hend : ∀ i : Fin 2,
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2))))
    (La V Dc : Set UnitTwoSphere)
    (hlevel : (⋃ i : Fin 2, range (q i)) = La)
    (hclosed : La ∩ Dc = ⋃ i : Fin 2, range (gamma i))
    (hopen : La ∩ V = ⋃ i : Fin 2, gamma i '' Ioo (0 : unitInterval) 1)
    (hNoBypass : ∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B Dc → B = ∅)
    (hChosenParent : range (gamma iTar) ⊆ range (q 0)) :
    ∃ (label : Fin 2 ≃ Fin 2) (a v : Fin 2 → ℝ) (eta : ℝ),
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun i t =>
      q (label i) (complexUnitCircleHomeomorph (Circle.exp (a i + v i * t)))
    (∀ i : Fin 2, IsCompact (range (q i)) ∧ IsCompact (La \ range (q i))) ∧
    Function.Injective p ∧ 0 < eta ∧ eta < 1 / 8 ∧
    (∀ i : Fin 2, range (gamma i) ⊆ range (q (label i))) ∧
    (∀ i : Fin 2,
      0 < |v i| ∧ |v i| < 2 * Real.pi ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha i) ∧
      (∀ t : ℝ, Function.Injective
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha i) t)) ∧
      Set.InjOn (alpha i) (Icc (-eta) (1 + eta)) ∧
      alpha i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      alpha i 1 = p (finProdFinEquiv (i, (1 : Fin 2))) ∧
      Disjoint (alpha i '' Ioo (0 : ℝ) 1) Dc ∧
      (alpha i '' Icc (0 : ℝ) 1) ∩ Dc =
        {p (finProdFinEquiv (i, (0 : Fin 2))),
          p (finProdFinEquiv (i, (1 : Fin 2)))} ∧
      (∀ s ∈ Ioo (-eta) (0 : ℝ), alpha i s ∈ V) ∧
      (∀ s ∈ Ioo (1 : ℝ) (1 + eta), alpha i s ∈ V)) ∧
    Disjoint (alpha 0 '' Icc (-eta) (1 + eta))
      (alpha 1 '' Icc (-eta) (1 + eta)) ∧
    La \ V = ⋃ i : Fin 2, alpha i '' Icc (0 : ℝ) 1 ∧
    La ∩ (Dc \ V) = range p ∧
    (∀ i : Fin 2,
      range (q (label i)) ∩ Dc = range (gamma i) ∧
      range (q (label i)) ∩ V = gamma i '' Ioo (0 : unitInterval) 1 ∧
      range (q (label i)) \ V = alpha i '' Icc (0 : ℝ) 1 ∧
      range (q (label i)) =
        (alpha i '' Icc (0 : ℝ) 1) ∪ range (gamma i)) ∧
    label.symm 0 = iTar := by
  classical
  obtain ⟨label, a, v, eta, hcompact, hp, heta, hetaSmall, hparent,
      harc, hdisjoint, hcover, hrim, heach⟩ :=
    exists_saddle_native_source_exterior_arcs q hq hqd gamma hgamma hgdisjoint p
      hend La V Dc hlevel hclosed hopen hNoBypass
  have hparentTar : range (gamma iTar) ⊆ range (q (label iTar)) :=
    hparent iTar
  have hnonempty : (range (gamma iTar)).Nonempty :=
    ⟨gamma iTar 0, mem_range_self _⟩
  have hlabelTar : label iTar = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := hnonempty
    exact disjoint_left.mp (hqd (label iTar) 0 hne)
      (hparentTar hy) (hChosenParent hy)
  have hlabelInv : label.symm 0 = iTar := by
    have hh := congrArg label.symm hlabelTar
    simpa using hh.symm
  refine ⟨label, a, v, eta, ?_⟩
  exact ⟨hcompact, hp, heta, hetaSmall, hparent, harc, hdisjoint,
    hcover, hrim, heach, hlabelInv⟩

theorem reference_lane_transport_unions
    (j : UnitTwoSphere → E3) (_hj : Function.Injective j)
    (T : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (alpha : Fin 2 → ℝ → UnitTwoSphere)
    (La V Dc : Set UnitTwoSphere) (p : Fin 4 → UnitTwoSphere)
    (Ext Rim : Set E3)
    (hSource : La \ V = ⋃ i : Fin 2, alpha i '' Icc (0 : ℝ) 1)
    (hSourceRim : La ∩ (Dc \ V) = range p)
    (hExterior : T '' (j '' (La \ V)) = Ext)
    (hExteriorInv : T.symm '' Ext = j '' (La \ V))
    (hRim : T '' (j '' (La ∩ (Dc \ V))) = Rim)
    (hRimInv : T.symm '' Rim = j '' (La ∩ (Dc \ V))) :
    let beta : Fin 2 → ℝ → E3 := fun i t => T (j (alpha i t))
    (⋃ i : Fin 2, beta i '' Icc (0 : ℝ) 1) = Ext ∧
    T.symm '' Ext = j '' (La \ V) ∧
    T '' (j '' (La ∩ (Dc \ V))) = Rim ∧
    T.symm '' Rim = j '' (range p) := by
  classical
  dsimp only
  let beta : Fin 2 → ℝ → E3 := fun i t => T (j (alpha i t))
  have himage (i : Fin 2) :
      beta i '' Icc (0 : ℝ) 1 =
        T '' (j '' (alpha i '' Icc (0 : ℝ) 1)) := by
    change (T ∘ j ∘ alpha i) '' Icc (0 : ℝ) 1 = _
    rw [image_comp, image_comp]
  have hsourceImage : j '' (La \ V) =
      ⋃ i : Fin 2, j '' (alpha i '' Icc (0 : ℝ) 1) := by
    rw [hSource, image_iUnion]
  have hforward : (⋃ i : Fin 2, beta i '' Icc (0 : ℝ) 1) = Ext := by
    calc
      (⋃ i : Fin 2, beta i '' Icc (0 : ℝ) 1) =
          ⋃ i : Fin 2, T '' (j '' (alpha i '' Icc (0 : ℝ) 1)) := by
            exact iUnion_congr fun i => himage i
      _ = T '' (⋃ i : Fin 2, j '' (alpha i '' Icc (0 : ℝ) 1)) := by
        rw [image_iUnion]
      _ = T '' (j '' (La \ V)) := by rw [← hsourceImage]
      _ = Ext := hExterior
  have hrimInv' : T.symm '' Rim = j '' (range p) := by
    rw [hRimInv, hSourceRim]
  exact ⟨hforward, hExteriorInv, hRim, hrimInv'⟩

theorem reference_lane_strict_exterior
    (j : UnitTwoSphere → E3) (hj : Function.Injective j)
    (T : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (alpha : Fin 2 → ℝ → UnitTwoSphere)
    (La V Dc : Set UnitTwoSphere) (Dtarget Rim : Set E3)
    (hSource : La \ V = ⋃ i : Fin 2, alpha i '' Icc (0 : ℝ) 1)
    (hOutside : ∀ i : Fin 2, ∀ t ∈ Ioo (0 : ℝ) 1,
      alpha i t ∉ Dc)
    (Ext : Set E3)
    (hExterior : T '' (j '' (La \ V)) = Ext)
    (hTargetRim : Ext ∩ Dtarget = Rim)
    (hRimInv : T.symm '' Rim = j '' (La ∩ (Dc \ V))) :
    ∀ i : Fin 2, ∀ t ∈ Ioo (0 : ℝ) 1,
      T (j (alpha i t)) ∉ Dtarget := by
  classical
  intro i t ht htarget
  have hExt : T (j (alpha i t)) ∈ Ext := by
    rw [← hExterior]
    have hsourceMem : alpha i t ∈ La \ V := by
      rw [hSource]
      apply mem_iUnion.mpr
      exact ⟨i, ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩⟩
    exact ⟨j (alpha i t), ⟨alpha i t, hsourceMem, rfl⟩, rfl⟩
  have hRimMem : T (j (alpha i t)) ∈ Rim := by
    rw [← hTargetRim]
    exact ⟨hExt, htarget⟩
  have hInvMem : T.symm (T (j (alpha i t))) ∈
      j '' (La ∩ (Dc \ V)) := by
    have hm : T.symm (T (j (alpha i t))) ∈ T.symm '' Rim :=
      ⟨T (j (alpha i t)), hRimMem, rfl⟩
    rw [hRimInv] at hm
    exact hm
  rcases hInvMem with ⟨z, hz, hEq⟩
  have hEq' : j (alpha i t) = j z := by
    simpa only [T.symm_apply_apply] using hEq.symm
  have hzAlpha : alpha i t = z := hj hEq'
  exact hOutside i t ht (hzAlpha ▸ hz.2.1)

theorem reference_lane_physical_normalized_unions
    (L : E3 ≃L[ℝ] (E2 × ℝ))
    (g : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (c : ℝ) (alphaE : Fin 2 → ℝ → E3) (Ext : Set E3)
    (hHorizontal : ∀ y ∈ Ext, (L y).2 = c)
    (hExtUnion : Ext = ⋃ i : Fin 2, alphaE i '' Icc (0 : ℝ) 1) :
    let alphaPhys : Fin 2 → ℝ → E2 := fun i t => (L (alphaE i t)).1
    let alphaNorm : Fin 2 → ℝ → E2 := fun i t =>
      g.symm (alphaPhys i t)
    let Eref : Set E2 := {x | L.symm (g x, c) ∈ Ext}
    (g '' Eref = ⋃ i : Fin 2, alphaPhys i '' Icc (0 : ℝ) 1) ∧
    (Eref = ⋃ i : Fin 2, alphaNorm i '' Icc (0 : ℝ) 1) := by
  classical
  dsimp only
  let alphaPhys : Fin 2 → ℝ → E2 := fun i t => (L (alphaE i t)).1
  let alphaNorm : Fin 2 → ℝ → E2 := fun i t =>
    g.symm (alphaPhys i t)
  let Eref : Set E2 := {x | L.symm (g x, c) ∈ Ext}
  have hmemExt (i : Fin 2) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) : alphaE i t ∈ Ext := by
    rw [hExtUnion]
    exact mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
  have hcoord (i : Fin 2) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) :
      L.symm (alphaPhys i t, c) = alphaE i t := by
    have hc := hHorizontal (alphaE i t) (hmemExt i t ht)
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext (by rfl) hc.symm
  have hphys : g '' Eref =
      ⋃ i : Fin 2, alphaPhys i '' Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change L.symm (g z, c) ∈ Ext at hz
      rw [hExtUnion] at hz
      obtain ⟨i, ⟨t, ht, hteq⟩⟩ := mem_iUnion.mp hz
      have hy : alphaE i t = L.symm (g z, c) := hteq
      have hfirst : alphaPhys i t = g z := by
        have hh := congrArg L hy
        rw [L.apply_symm_apply] at hh
        exact congrArg Prod.fst hh
      rw [← hfirst]
      exact mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
    · intro hx
      obtain ⟨i, ⟨t, ht, hxt⟩⟩ := mem_iUnion.mp hx
      refine ⟨alphaNorm i t, ?_, ?_⟩
      · change L.symm (g (g.symm (alphaPhys i t)), c) ∈ Ext
        rw [g.apply_symm_apply]
        rw [hcoord i t ht]
        exact hmemExt i t ht
      · simpa [alphaNorm] using hxt
  have hnorm : Eref =
      ⋃ i : Fin 2, alphaNorm i '' Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      change L.symm (g x, c) ∈ Ext at hx
      have hy : L.symm (g x, c) ∈ Ext := hx
      rw [hExtUnion] at hy
      obtain ⟨i, ⟨t, ht, hty⟩⟩ := mem_iUnion.mp hy
      have hfirst : alphaPhys i t = g x := by
        have hh := congrArg L hty.symm
        rw [L.apply_symm_apply] at hh
        exact (congrArg Prod.fst hh).symm
      apply mem_iUnion.mpr
      refine ⟨i, ⟨t, ht, ?_⟩⟩
      change g.symm (alphaPhys i t) = x
      rw [hfirst, g.symm_apply_apply]
    · intro hx
      obtain ⟨i, ⟨t, ht, hxt⟩⟩ := mem_iUnion.mp hx
      change L.symm (g x, c) ∈ Ext
      rw [← hxt]
      simp only [alphaNorm, g.apply_symm_apply]
      rw [hcoord i t ht]
      exact hmemExt i t ht
  exact ⟨hphys, hnorm⟩

theorem reference_native_upper_level_image (d k delta : ℝ) :
    let j : UnitTwoSphere → E3 := fun q =>
      nestedReferenceDiffeomorph d (q : E3)
    let H : E3 → ℝ := fun y => (heightCoordinates y).2
    j '' {q : UnitTwoSphere | H (j q) = k + d + delta} =
      (nestedReferenceBallChart d).boundary ∩
        {y : E3 | (heightCoordinates y).2 = k + delta + d} := by
  classical
  dsimp only
  let j : UnitTwoSphere → E3 := fun q =>
    nestedReferenceDiffeomorph d (q : E3)
  let H : E3 → ℝ := fun y => (heightCoordinates y).2
  change j '' {q : UnitTwoSphere | H (j q) = k + d + delta} =
    (nestedReferenceBallChart d).boundary ∩
      {y : E3 | (heightCoordinates y).2 = k + delta + d}
  let psi : UnitTwoSphere × ℝ → E3 := fun p =>
    nestedReferenceDiffeomorph d ((1 + p.2) • (p.1 : E3))
  have hpsi0 : (fun q : UnitTwoSphere => psi (q, 0)) = j := by
    funext q
    simp only [psi, j, add_zero, one_smul]
  obtain ⟨_, hS, _, _⟩ := exists_nestedReference_collar d
  have hjS : range j = (nestedReferenceBallChart d).boundary := by
    simpa only [← hpsi0] using hS
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hjS ▸ mem_range_self q, ?_⟩
    change H (j q) = k + d + delta at hq
    change (heightCoordinates (j q)).2 = k + delta + d
    dsimp only [H] at hq ⊢
    linarith only [hq]
  · rintro ⟨hy, hh⟩
    have hy' : y ∈ range j := hjS.symm ▸ hy
    obtain ⟨q, rfl⟩ := hy'
    refine ⟨q, ?_, rfl⟩
    change H (j q) = k + d + delta
    dsimp only [H]
    change (heightCoordinates (j q)).2 = k + delta + d at hh
    linarith only [hh]

theorem reference_native_no_bypass_of_retained_roots
    (ws wm d rho delta : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta < rho ^ 2)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (T : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) :
    let k : ℝ := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
    let mu : ℝ := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
    let V : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
    let C : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let La : Set UnitTwoSphere := {q |
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d - delta}
    let Lb : Set UnitTwoSphere := {q |
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d + delta}
    (hbuffer : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ⊆ e.target) →
    (hheight : ∀ q ∈ e.source,
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d - (e q).1 ^ 2 + (e q).2 ^ 2) →
    k + delta < mu →
    IsOpen V →
    IsCompact C →
    T '' ((fun q : UnitTwoSphere => nestedReferenceDiffeomorph d (q : E3)) ''
      (La \ V)) =
      (fun q : UnitTwoSphere => nestedReferenceDiffeomorph d (q : E3)) ''
        (Lb \ V) →
    T '' ((fun q : UnitTwoSphere => nestedReferenceDiffeomorph d (q : E3)) ''
      (La ∩ (C \ V))) =
      (fun q : UnitTwoSphere => nestedReferenceDiffeomorph d (q : E3)) ''
        (Lb ∩ (C \ V)) →
    ∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B C → B = ∅ := by
  classical
  dsimp only
  intro hbuffer hheight hupper hV hC hExterior hRim
  let j : UnitTwoSphere → E3 := fun q =>
    nestedReferenceDiffeomorph d (q : E3)
  let H : E3 → ℝ := fun y => (heightCoordinates y).2
  have hj : Continuous j :=
    (nestedReferenceDiffeomorph d).continuous.comp continuous_subtype_val
  have hji : Function.Injective j :=
    (nestedReferenceDiffeomorph d).injective.comp Subtype.val_injective
  have hH : Continuous H := heightCoordinates.continuous.snd
  have hlevel := reference_native_upper_level_image d
    (1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32) delta
  dsimp only at hlevel
  have hconn0 :=
    saddle_nested_reference_positive_level_connected_of_roots ws wm
      hwslo hwshi hwsroot hwmlo hwmhi hwmroot d
      (1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 + delta)
      (by linarith only [hdelta]) hupper
  have hconn : IsPreconnected (j ''
      {q : UnitTwoSphere | H (j q) =
        1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 + d + delta}) := by
    rw [hlevel]
    exact hconn0.isPreconnected
  have hnb := saddle_nested_native_no_bypass j hj hji H hH e
    (1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 + d) rho delta
    hrho hdelta hsmall hbuffer (by
      intro q hq
      exact hheight q hq) T
  exact hnb hV hC hconn hExterior hRim

theorem exists_reference_lane_selected_sign_parent
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (k d rho delta : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta) (hsmall : delta < rho ^ 2)
    (hdisc : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ⊆ e.target)
    (hheight : ∀ p ∈ e.source,
      (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 =
        k + d - (e p).1 ^ 2 + (e p).2 ^ 2)
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ i : Fin 2, Continuous (q i))
    (hqd : Disjoint (range (q 0)) (range (q 1)))
    (iTar : Fin 2) :
    let La : Set UnitTwoSphere := {p |
      (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 =
        k + d - delta}
    let Dc : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let aa : ℝ := Real.sqrt ((rho ^ 2 - delta) / 2)
    let sg : Fin 2 → ℝ := ![1, -1]
    let v : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
    let gamma : ℝ → Fin 2 → unitInterval → UnitTwoSphere := fun sigma i t =>
      e.symm (sigma * sg i * Real.sqrt ((v t) ^ 2 + delta),
        sigma * sg i * v t)
    ((⋃ i : Fin 2, range (q i)) = La) →
    (∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B Dc → B = ∅) →
    ∃ iPos : Fin 2, ∃ sigma : ℝ,
      (iPos = 0 ↔ e.symm (Real.sqrt delta, 0) ∈ range (q 0)) ∧
      (iPos = 1 ↔ e.symm (-Real.sqrt delta, 0) ∈ range (q 0)) ∧
      (sigma = 1 ∨ sigma = -1) ∧
      sigma = (if iPos = iTar then 1 else -1) ∧
      range (gamma sigma iTar) ⊆ range (q 0) := by
  classical
  dsimp only
  intro hlevel hNoBypass
  let Dc : Set UnitTwoSphere := e.symm ''
    {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
  let aa : ℝ := Real.sqrt ((rho ^ 2 - delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let v : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let gamma : ℝ → Fin 2 → unitInterval → UnitTwoSphere := fun sigma i t =>
    e.symm (sigma * sg i * Real.sqrt ((v t) ^ 2 + delta),
      sigma * sg i * v t)
  have hInc := exists_saddle_nested_reference_inner_connector_incidence
    e k d rho delta hrho hdelta hsmall hdisc hheight q hq hqd hlevel hNoBypass
  obtain ⟨iPos, hiPos0, hiPos1, hRest⟩ := hInc
  obtain ⟨_, hInter, hTarget⟩ := hRest
  have hSelected := hTarget iTar
  dsimp only at hSelected
  obtain ⟨hsigma, hiRef, _⟩ := hSelected
  let sigma : ℝ := if iPos = iTar then 1 else -1
  have hSigma : sigma = 1 ∨ sigma = -1 := by
    simpa only [sigma] using hsigma
  have hSigmaRef : (if sigma = 1 then iPos else
      if iPos = 0 then 1 else 0) = iTar := by
    simpa only [sigma] using hiRef
  have hParentEq : range (q 0) ∩ Dc = range (gamma sigma iTar) := by
    have hh := hInter sigma hSigma
    simpa only [Dc, gamma, v, aa, sg, hSigmaRef] using hh.1
  have hParent : range (gamma sigma iTar) ⊆ range (q 0) := by
    intro y hy
    have hy' : y ∈ range (q 0) ∩ Dc := by
      rw [hParentEq]
      exact hy
    exact hy'.1
  exact ⟨iPos, sigma, hiPos0, hiPos1, hSigma, rfl, hParent⟩

theorem exists_reference_signed_endpoint_source_charts
    (rho delta : ℝ) (hrho : 0 < rho)
    (_hdelta : 0 < delta) (hdeltaSmall : delta ≤ rho ^ 2 / 128)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (sx sy : Fin 4 → ℝ)
    (hsx : ∀ i : Fin 4, (sx i) ^ 2 = 1)
    (hsy : ∀ i : Fin 4, (sy i) ^ 2 = 1) :
    let U : Set (ℝ × ℝ) :=
      Ioo (-2 * delta) (2 * delta) ×ˢ
        Ioo (-(1 / 8 : ℝ)) (1 / 8)
    ∃ X : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      ∀ i : Fin 4,
        (X i).source = U ∧
        (X i).target ⊆ {v : ℝ × ℝ |
          0 < sigma * sy i * v.1 ∧ 0 < sigma * sx i * v.2} ∧
        ContDiffOn ℝ ∞ (X i) U ∧
        ContDiffOn ℝ ∞ (X i).symm (X i).target ∧
        (∀ p ∈ U, (X i) p =
          (sigma * sy i * Real.sqrt
              ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2),
            sigma * sx i * Real.sqrt
              ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2))) ∧
        (∀ v : ℝ × ℝ, (X i).symm v =
          (-v.1 ^ 2 + v.2 ^ 2,
            Real.sqrt (v.1 ^ 2 + v.2 ^ 2) / rho - 1)) ∧
        (∀ p ∈ U,
          ((X i) p).1 ^ 2 + ((X i) p).2 ^ 2 =
              rho ^ 2 * (1 + p.2) ^ 2 ∧
          -((X i) p).1 ^ 2 + ((X i) p).2 ^ 2 = p.1) := by
  classical
  dsimp only
  have hsigmaSq : sigma ^ 2 = 1 := by
    rcases hsigma with h | h <;> simp [h]
  let U : Set (ℝ × ℝ) := Ioo (-2 * delta) (2 * delta) ×ˢ
    Ioo (-(1 / 8 : ℝ)) (1 / 8)
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUsource (p : ℝ × ℝ) (hp : p ∈ U) :
      -1 < p.2 ∧ |p.1| < rho ^ 2 * (1 + p.2) ^ 2 := by
    have hp1 := hp.1
    have hp2 := hp.2
    have hrad : 2 * delta < rho ^ 2 * (1 + p.2) ^ 2 := by
      have hpos : 0 < 1 + p.2 := by linarith [hp2.1]
      have hz : 0 < p.2 + 1 / 8 := by linarith [hp2.1]
      have hbase : (1 : ℝ) / 2 < (1 + p.2) ^ 2 := by
        have hpz : 0 < 7 / 4 + (p.2 + 1 / 8) := by linarith [hp2.1]
        have hprod := mul_pos hz hpz
        nlinarith only [hprod]
      have hrhosq : 0 < rho ^ 2 := sq_pos_of_pos hrho
      have htwo : 2 * delta ≤ rho ^ 2 / 64 := by
        nlinarith only [hdeltaSmall]
      nlinarith only [hbase, hrhosq, htwo]
    exact ⟨by linarith [hp2.1], by
      rw [abs_lt]
      exact ⟨by linarith [hp1.1], by linarith [hp1.2, hrad]⟩⟩
  choose Y hYsource hYtarget hYforward hYinverse hYsmooth hYinvSmooth
    hYformula using fun i : Fin 4 =>
      exists_signed_hyperbola_chart rho (sigma * sy i) (sigma * sx i) hrho
        (by simp [mul_pow, hsigmaSq, hsy i])
        (by simp [mul_pow, hsigmaSq, hsx i])
  let X : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := fun i =>
    (Y i).restrOpen U hUopen
  have hXsource (i : Fin 4) : (X i).source = U := by
    change ((Y i).restrOpen U hUopen).source = U
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact inter_eq_right.mpr (fun p hp => hYsource i ▸ hUsource p hp)
  have hXtarget (i : Fin 4) : (X i).target ⊆
      {v : ℝ × ℝ | 0 < sigma * sy i * v.1 ∧
        0 < sigma * sx i * v.2} := by
    intro y hy
    rw [← (X i).image_source_eq_target, hXsource] at hy
    rcases hy with ⟨p, hp, rfl⟩
    have hpY : p ∈ (Y i).source := by
      rw [hYsource i]
      exact hUsource p hp
    have hyY : (Y i) p ∈ (Y i).target := (Y i).map_source hpY
    rw [hYtarget i] at hyY
    exact hyY
  have hXsmooth (i : Fin 4) : ContDiffOn ℝ ∞ (X i) U := by
    change ContDiffOn ℝ ∞ (Y i) U
    exact (hYsmooth i).mono (fun p hp => by
      rw [hYsource i]
      exact hUsource p hp)
  have hXtargetSubsetY (i : Fin 4) :
      (X i).target ⊆ (Y i).target := by
    intro y hy
    rw [← (X i).image_source_eq_target, hXsource] at hy
    rcases hy with ⟨p, hp, rfl⟩
    apply (Y i).map_source
    rw [hYsource i]
    exact hUsource p hp
  have hXinvSmooth (i : Fin 4) :
      ContDiffOn ℝ ∞ (X i).symm (X i).target := by
    change ContDiffOn ℝ ∞ (Y i).symm (X i).target
    exact (hYinvSmooth i).mono (hXtargetSubsetY i)
  refine ⟨X, fun i => ⟨hXsource i, hXtarget i, hXsmooth i,
    hXinvSmooth i, ?_, hYinverse i, ?_⟩⟩
  · intro p hp
    have hpY : p ∈ (Y i).source := by
      rw [hYsource i]
      exact hUsource p hp
    exact hYforward i p
  · intro p hp
    have hpY : p ∈ (Y i).source := by
      rw [hYsource i]
      exact hUsource p hp
    exact hYformula i p hpY

end PoincareConjecture.M25.Topology3D
