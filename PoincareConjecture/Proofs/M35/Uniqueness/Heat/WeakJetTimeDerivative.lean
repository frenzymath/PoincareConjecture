import PoincareConjecture.Proofs.M35.Uniqueness.Heat.WeakTimeDerivative









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem weakJet_hasDerivAt_of_nil
    (q p : ℝ → List (Fin n) → L2) {a b : ℝ} {m : ℕ}
    (hq : ∀ t ∈ Ioo a b, IsWeakSchwartzJet (q t) m)
    (hp : ∀ t ∈ Ioo a b, IsWeakSchwartzJet (p t) m)
    (hpc : ∀ w, w.length ≤ m → ContinuousOn (fun t => p t w) (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt (fun s => q s []) (p t []) t)
    (w : List (Fin n)) (hw : w.length ≤ m) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => q s w) (p t w) t := by
  have hscalar : ∀ v : List (Fin n), v.length ≤ m → ∀ s ∈ Ioo a b,
      ∀ φ : 𝓢(V, ℝ), HasDerivAt (fun r => inner ℝ (q r v) (φ.toLp 2 volume))
        (inner ℝ (p s v) (φ.toLp 2 volume)) s := by
    intro v
    induction v with
    | nil =>
      intro _ s hs φ
      simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
        (innerSL ℝ (φ.toLp 2 volume)).hasFDerivAt.comp_hasDerivAt s (hd s hs)
    | cons i v ih =>
      intro hv s hs φ
      have hv' : v.length < m := by simp only [List.length_cons] at hv; omega
      have hneg := (ih (by omega) s hs (∂_{EuclideanSpace.single i (1 : ℝ)} φ)).neg
      have hvalue := (hp s hs v hv' i φ).symm
      apply (hneg.congr_deriv hvalue).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact hq r hr v hv' i φ
  exact hasDerivAt_of_dense_test_derivatives
    (fun φ : 𝓢(V, ℝ) => φ.toLp 2 volume)
    (SchwartzMap.denseRange_toLpCLM (F := ℝ) (μ := (volume : Measure V))
      (by norm_num : (2 : ENNReal) ≠ ⊤))
    (fun s => q s w) (fun s => p s w) ht (hpc w hw) (hscalar w hw)

end PoincareConjecture.M35.Uniqueness.Heat
