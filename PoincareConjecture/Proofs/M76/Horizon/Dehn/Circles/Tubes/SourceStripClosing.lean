import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentSourceStrips
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisPermutations

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem signedSheetStripMap_closing (closing : SignedAxisPermutation)
    (j : Fin 2) (u a b : ℝ) :
    signedSheetStripMap (closing.index j) ((if closing.sign j.rev then u else -u), b) =
      (closing.linear (signedSheetStripMap j (u, a)).1, b) := by
  rcases closing with ⟨swap, sign⟩
  cases swap <;> fin_cases j <;> cases h0 : sign 0 <;> cases h1 : sign 1 <;>
    simp [signedSheetStripMap_apply, SignedAxisPermutation.index, jointSheetIndex,
      SignedAxisPermutation.linear_apply, h0, h1, Fin.rev]

theorem signed_sheet_coordinate_eq_iff (closing : SignedAxisPermutation)
    (j k : Fin 2) (u v : ℝ) :
    closing.linear (signedSheetStripMap j (u, 0)).1 =
        (signedSheetStripMap k (v, 0)).1 ↔
      (k = closing.index j ∧ v = (if closing.sign j.rev then u else -u)) ∨
        (u = 0 ∧ v = 0) := by
  rcases closing with ⟨swap, sign⟩
  cases swap <;> fin_cases j <;> fin_cases k <;>
    cases h0 : sign 0 <;> cases h1 : sign 1 <;>
    simp [signedSheetStripMap_apply, SignedAxisPermutation.index, jointSheetIndex,
      SignedAxisPermutation.linear_apply, h0, h1, Fin.rev] <;> aesop

theorem source_strip_closing_of_physical_closing
    {X E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : Set F} (f : F → X) (inverse : E → X) (sigma : P2 × ℝ → E)
    {a b : ℝ} (hab : a < b) (closing : SignedAxisPermutation)
    (hclosing : ∀ x ∈ signedTubeDiamond, sigma (x, a) = sigma (closing.linear x, b))
    (phi : Fin 2 → P2 → F)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-1 : ℝ) 1 ×ˢ Icc a b))
    (hD : ∀ j, MapsTo (phi j) (Icc (-1 : ℝ) 1 ×ˢ Icc a b) S)
    (hvalue : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      f (phi j z) = inverse (sigma (signedSheetStripMap j z)))
    (hunique : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b → z.1 ≠ 0 →
      ∀ w ∈ S, f w = inverse (sigma (signedSheetStripMap j z)) → w = phi j z) :
    ∀ j u, u ∈ Icc (-1 : ℝ) 1 →
      phi j (u, a) = phi (closing.index j) ((if closing.sign j.rev then u else -u), b) := by
  intro j
  let negated : ℝ → ℝ := fun u => if closing.sign j.rev then u else -u
  have hneg : Continuous negated := by
    dsimp only [negated]
    split <;> fun_prop
  have hnegmem (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) : negated u ∈ Icc (-1 : ℝ) 1 := by
    dsimp only [negated]
    split
    · exact hu
    · constructor <;> linarith [hu.1, hu.2]
  have hleft (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      (u, a) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b := ⟨hu, le_rfl, hab.le⟩
  have hright (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      (negated u, b) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b := ⟨hnegmem u hu, hab.le, le_rfl⟩
  apply eqOn_transverse_interval_of_eq_ne_zero (by norm_num : (0 : ℝ) < 1)
    ((hPL j).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hleft)
    ((hPL (closing.index j)).continuousOn.comp (hneg.prodMk continuous_const).continuousOn hright)
  intro u hu hne
  apply (hunique j (u, a) (hleft u hu) hne _ (hD _ (hright u hu)) ?_).symm
  rw [hvalue _ _ (hright u hu)]
  change inverse (sigma (signedSheetStripMap (closing.index j)
    ((if closing.sign j.rev then u else -u), b))) = _
  rw [signedSheetStripMap_closing closing j u a b]
  simpa only [signedSheetStripMap_apply] using
    congrArg inverse (hclosing _ (signedSheetStripMap_mem j (hleft u hu)).1).symm

theorem source_axis_fibers_of_signed_tube
    {E F : Type*} (sigma : P2 × ℝ → E) {a b : ℝ} (hab : a < b)
    (closing : SignedAxisPermutation)
    (hfib : ∀ x y : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = a ∧ (y : P2 × ℝ).2 = b ∧
          closing.linear (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = a ∧ (x : P2 × ℝ).2 = b ∧
          closing.linear (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (phi : Fin 2 → P2 → F) (graph : F → E)
    (hgraph : ∀ j s, s ∈ Icc a b → graph (phi j (0, s)) = sigma ((0, 0), s))
    (hsep : ∀ j s, s ∈ Icc a b → phi j (0, s) ≠ phi j.rev (0, s))
    (hclose : ∀ j, phi j (0, a) = phi (closing.index j) (0, b)) :
    ∀ j k (s t : Icc a b),
      phi j (0, s) = phi k (0, t) ↔
        (j = k ∧ s = t) ∨
        ((s : ℝ) = a ∧ (t : ℝ) = b ∧ k = closing.index j) ∨
        ((t : ℝ) = a ∧ (s : ℝ) = b ∧ j = closing.index k) := by
  have hindex (j k : Fin 2) (s : ℝ) (hs : s ∈ Icc a b)
      (heq : phi j (0, s) = phi k (0, s)) : j = k := by
    by_contra hne
    have hk : k = j.rev := by fin_cases j <;> fin_cases k <;> simp_all [Fin.rev]
    exact hsep j s hs (hk ▸ heq)
  have hzero : (0, 0) ∈ signedTubeDiamond := by
    rw [signedTubeDiamond_coordinate_iff]
    norm_num
  intro j k s t
  constructor
  · intro heq
    have hphysical : sigma ((0, 0), (s : ℝ)) = sigma ((0, 0), (t : ℝ)) :=
      (hgraph j s s.property).symm.trans ((congrArg graph heq).trans (hgraph k t t.property))
    rcases (hfib ⟨((0, 0), s), hzero, s.property⟩
      ⟨((0, 0), t), hzero, t.property⟩).mp hphysical with h | h | h
    · have hst : s = t := Subtype.ext (congrArg
        (fun z : ↥(signedTubeDiamond ×ˢ Icc a b) => (z : P2 × ℝ).2) h)
      subst t
      exact Or.inl ⟨hindex j k s s.property heq, rfl⟩
    · change (s : ℝ) = a ∧ (t : ℝ) = b ∧ _ at h
      have heq' : phi (closing.index j) (0, b) = phi k (0, b) := by
        rw [h.1, h.2.1] at heq
        exact (hclose j).symm.trans heq
      exact Or.inr (Or.inl ⟨h.1, h.2.1, (hindex _ _ b ⟨hab.le, le_rfl⟩ heq').symm⟩)
    · change (t : ℝ) = a ∧ (s : ℝ) = b ∧ _ at h
      have heq' : phi (closing.index k) (0, b) = phi j (0, b) := by
        rw [h.1, h.2.1] at heq
        exact (hclose k).symm.trans heq.symm
      exact Or.inr (Or.inr ⟨h.1, h.2.1, (hindex _ _ b ⟨hab.le, le_rfl⟩ heq').symm⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨hs, ht, rfl⟩ | ⟨ht, hs, rfl⟩)
    · rfl
    · rw [hs, ht]
      exact hclose j
    · rw [hs, ht]
      exact (hclose k).symm

theorem source_strip_injOn_open_of_signed_tube
    {E F : Type*} (sigma : P2 × ℝ → E) {a b : ℝ}
    (closing : SignedAxisPermutation)
    (hfib : ∀ x y : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = a ∧ (y : P2 × ℝ).2 = b ∧
          closing.linear (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = a ∧ (x : P2 × ℝ).2 = b ∧
          closing.linear (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (phi : Fin 2 → P2 → F) (graph : F → E)
    (hgraph : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      graph (phi j z) = sigma (signedSheetStripMap j z)) :
    ∀ j, InjOn (phi j) (Ioo (-1 : ℝ) 1 ×ˢ Ioo a b) := by
  intro j z hz w hw heq
  have hz' : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
  have hw' : w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
    ⟨⟨hw.1.1.le, hw.1.2.le⟩, hw.2.1.le, hw.2.2.le⟩
  have heq' := (hgraph j z hz').symm.trans ((congrArg graph heq).trans (hgraph j w hw'))
  rcases (hfib ⟨_, signedSheetStripMap_mem j hz'⟩
    ⟨_, signedSheetStripMap_mem j hw'⟩).mp heq' with h | h | h
  · have hv := congrArg Subtype.val h
    apply Prod.ext
    · have hcoord := congrArg (fun q : P2 × ℝ => if j = 0 then q.1.2 else q.1.1) hv
      fin_cases j <;> simpa [signedSheetStripMap_apply] using hcoord
    · simpa only [signedSheetStripMap_apply] using congrArg Prod.snd hv
  · exact (hz.2.1.ne' (by simpa only [signedSheetStripMap_apply] using h.1)).elim
  · exact (hw.2.1.ne' (by simpa only [signedSheetStripMap_apply] using h.1)).elim

end PoincareConjecture.M76.Dehn
