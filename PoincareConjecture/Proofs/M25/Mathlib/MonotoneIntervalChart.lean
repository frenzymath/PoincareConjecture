import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set
open scoped ContDiff




theorem StrictMonoOn.exists_smooth_openInterval_chart
    {f : ℝ → ℝ} {a b : ℝ}
    (hmono : StrictMonoOn f (Icc a b))
    (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Icc a b))
    (hderiv : ∀ s ∈ Ioo a b, 0 < deriv f s) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = Ioo a b ∧
      e.target = Ioo (f a) (f b) ∧
      (e : ℝ → ℝ) = f ∧
      ContDiffOn ℝ ∞ (e : ℝ → ℝ) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ r ∈ e.target,
        0 < deriv (e.symm : ℝ → ℝ) r ∧
        deriv (e.symm : ℝ → ℝ) r =
          (deriv f (e.symm r))⁻¹) := by
  classical
  have hf' : ContDiffOn ℝ ∞ f (Ioo a b) := hf.mono Ioo_subset_Icc_self
  have hmono' : StrictMonoOn f (Ioo a b) := hmono.mono Ioo_subset_Icc_self
  have himage : f '' Ioo a b = Ioo (f a) (f b) :=
    hf.continuousOn.image_Ioo_of_strictMonoOn hab.le hmono
  have hstrict : StrictMono ((Ioo a b).domRestrict f) :=
    fun x y hxy => hmono' x.property y.property hxy
  have hrange : range ((Ioo a b).domRestrict f) = Ioo (f a) (f b) := by
    rw [range_domRestrict, himage]
  have hemb := hstrict.isEmbedding_of_ordConnected (by rw [hrange]; infer_instance)
  have hopen : Topology.IsOpenEmbedding ((Ioo a b).domRestrict f) :=
    ⟨hemb, by rw [hrange]; exact isOpen_Ioo⟩
  let pe := Set.InjOn.toPartialEquiv f (Ioo a b) hmono'.injOn
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe
    hf'.continuousOn hopen.isOpenMap isOpen_Ioo
  refine ⟨e, rfl, himage, rfl, hf', ?_, ?_⟩
  · intro y hy
    have hx : e.symm y ∈ Ioo a b := e.map_target hy
    have hF : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm y) :=
      hf'.contDiffAt (isOpen_Ioo.mem_nhds hx)
    exact (e.contDiffAt_symm_deriv (hderiv _ hx).ne' hy
      (hF.differentiableAt (by simp)).hasDerivAt hF).contDiffWithinAt
  · intro y hy
    have hx : e.symm y ∈ Ioo a b := e.map_target hy
    have hF : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm y) :=
      hf'.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd := e.hasDerivAt_symm hy (hderiv _ hx).ne'
      (hF.differentiableAt (by simp)).hasDerivAt
    exact ⟨hd.deriv.symm ▸ inv_pos.mpr (hderiv _ hx), hd.deriv⟩
