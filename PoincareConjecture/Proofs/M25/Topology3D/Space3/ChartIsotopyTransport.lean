import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartConjugation
import Mathlib.Analysis.Calculus.ContDiff.Comp











set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (e : OpenPartialHomeomorph E F)
variable (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)

include he hi



theorem chartConjugateMap_contDiff_family (f : ℝ → E → E)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (hmap : ∀ t, MapsTo (f t) e.source e.source)
    {C : Set E} (hC : IsCompact C) (hCs : C ⊆ e.source)
    (hfix : ∀ t x, x ∉ C → f t x = x) :
    ContDiff ℝ ∞ (fun p : ℝ × F => chartConjugateMap e (f p.1) p.2) := by
  have himage : IsCompact (e '' C) := hC.image_of_continuousOn (e.continuousOn.mono hCs)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 ∈ e.target
  · have hinner : ContDiffAt ℝ ∞ (fun q : ℝ × F => e.symm q.2) p :=
      (hi.contDiffAt (e.open_target.mem_nhds hp)).comp p contDiffAt_snd
    have hmiddle : ContDiffAt ℝ ∞ (fun q : ℝ × F => f q.1 (e.symm q.2)) p :=
      hf.contDiffAt.comp p (contDiffAt_fst.prodMk hinner)
    have houter := (he.contDiffAt (e.open_source.mem_nhds
      (hmap p.1 (e.map_target hp)))).comp p hmiddle
    apply houter.congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × F in 𝓝 p, q.2 ∈ e.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact chartConjugateMap_of_mem e (f q.1) hq
  · have hpC : p.2 ∉ e '' C := by
      rintro ⟨x, hx, heq⟩
      exact hp (heq ▸ e.map_source (hCs hx))
    apply (contDiffAt_snd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × F → F) p).congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × F in 𝓝 p, q.2 ∉ e '' C :=
      continuous_snd.continuousAt.preimage_mem_nhds (himage.isClosed.isOpen_compl.mem_nhds hpC)
    filter_upwards [hn] with q hq
    exact chartConjugateMap_eq_self e (f q.1) (hfix q.1) hq


theorem chartConjugateMap_contDiff (f : E → E) (hf : ContDiff ℝ ∞ f)
    (hmap : MapsTo f e.source e.source) {C : Set E}
    (hC : IsCompact C) (hCs : C ⊆ e.source) (hfix : ∀ x ∉ C, f x = x) :
    ContDiff ℝ ∞ (chartConjugateMap e f) := by
  have h := chartConjugateMap_contDiff_family e he hi (fun _ => f)
    (hf.comp contDiff_snd) (fun _ => hmap) hC hCs (fun _ => hfix)
  simpa only [Function.comp_def, id_eq] using
    h.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)




noncomputable def chartConjugateDiffeomorph
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {C : Set E} (hC : IsCompact C) (hCs : C ⊆ e.source)
    (hfix : ∀ x ∉ C, f x = x) : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞ := by
  have hfixi : ∀ x ∉ C, f.symm x = x :=
    fun x hx => equiv_symm_fixed_of_fixed f.toEquiv (hfix x hx)
  have hmap : MapsTo f e.source e.source := equiv_mapsTo_of_fixed_compl f.toEquiv
    (fun x hx => hfix x (fun h => hx (hCs h)))
  have hmapi : MapsTo f.symm e.source e.source :=
    equiv_mapsTo_of_fixed_compl f.symm.toEquiv
      (fun x hx => hfixi x (fun h => hx (hCs h)))
  exact {
    toEquiv := chartConjugateEquiv e f.toEquiv hmap hmapi
    contMDiff_toFun := (chartConjugateMap_contDiff e he hi f f.contDiff hmap hC hCs hfix).contMDiff
    contMDiff_invFun :=
      (chartConjugateMap_contDiff e he hi f.symm f.symm.contDiff hmapi hC hCs hfixi).contMDiff }



theorem chartConjugateDiffeomorph_apply
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {C : Set E} (hC : IsCompact C) (hCs : C ⊆ e.source)
    (hfix : ∀ x ∉ C, f x = x) (y : F) :
    chartConjugateDiffeomorph e he hi f hC hCs hfix y = chartConjugateMap e f y := rfl



theorem exists_chart_transport_isotopy
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hΦ : ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2)) (hzero : ∀ x, Φ 0 x = x)
    {C : Set E} (hC : IsCompact C) (hCs : C ⊆ e.source)
    (hfix : ∀ t x, x ∉ C → Φ t x = x) :
    ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
      ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
      (∀ y, Ψ 0 y = y) ∧
      (∀ t x, x ∈ e.source → Ψ t (e x) = e (Φ t x)) ∧
      (∀ t y, y ∉ e '' C → Ψ t y = y) ∧ IsCompact (e '' C) ∧ e '' C ⊆ e.target := by
  let Ψ := fun t => chartConjugateDiffeomorph e he hi (Φ t) hC hCs (hfix t)
  refine ⟨Ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chartConjugateMap_contDiff_family e he hi (fun t => Φ t) hΦ
      (fun t => equiv_mapsTo_of_fixed_compl (Φ t).toEquiv
        (fun x hx => hfix t x (fun h => hx (hCs h)))) hC hCs hfix
  · intro y
    change chartConjugateMap e (Φ 0) y = y
    by_cases hy : y ∈ e.target
    · rw [chartConjugateMap_of_mem e (Φ 0) hy, hzero, e.right_inv hy]
    · classical
      simp only [chartConjugateMap, if_neg hy]
  · intro t x hx
    exact chartConjugateMap_apply_chart e (Φ t) hx
  · intro t y hy
    exact chartConjugateMap_eq_self e (Φ t) (hfix t) hy
  · exact hC.image_of_continuousOn (e.continuousOn.mono hCs)
  · rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hCs hx)

end PoincareConjecture.M25.Topology3D
