import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ChartHessianCoefficients
import PoincareConjecture.Proofs.M09.CompactFieldExtension










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "E" => EuclideanSpace ℝ (Fin n)




theorem flow_pullback_metric_hessian_contDiffOn {a b : ℝ} (F : RicciFlow n M (Icc a b))
    {U : Set V} (hU : IsOpen U) {ρ : V → M}
    (hρ : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ ρ U)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × V) × V => (F.metric z.1.1).inner (ρ z.1.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)) ((Icc a b ×ˢ U) ×ˢ univ) ∧
    ContDiffOn ℝ ∞
      (fun z : (ℝ × V) × V => (F.connection z.1.1).hessian f (ρ z.1.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)) ((Icc a b ×ˢ U) ×ˢ univ) := by
  let S : Set ((ℝ × V) × V) := (Icc a b ×ˢ U) ×ˢ univ
  suffices hlocal : ∀ z ∈ S,
      ContDiffWithinAt ℝ ∞
        (fun w : (ℝ × V) × V => (F.metric w.1.1).inner (ρ w.1.2)
          (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)
          (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)) S z ∧
      ContDiffWithinAt ℝ ∞
        (fun w : (ℝ × V) × V => (F.connection w.1.1).hessian f (ρ w.1.2)
          (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)
          (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)) S z from
    ⟨fun z hz => (hlocal z hz).1, fun z hz => (hlocal z hz).2⟩
  intro z hz
  let p := ρ z.1.2
  let c := chartAt E p
  let O := U ∩ ρ ⁻¹' c.source
  have hO : IsOpen O := hρ.continuousOn.isOpen_inter_preimage hU c.open_source
  have hzO : z.1.2 ∈ O := ⟨hz.1.2, mem_chart_source E p⟩
  let ψ : V → E := c ∘ ρ
  have hψ : ContDiffOn ℝ ∞ ψ O :=
    ((contMDiffOn_chart (I := 𝓡 n) (x := p)).comp
      (hρ.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hDψ := hψ.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hderiv (x : V) (hx : x ∈ O) :
      fderiv ℝ ψ x = (mfderiv (𝓡 n) (𝓡 n) c (ρ x)).comp
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ x) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp x ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hx.2)
      ((hρ.contMDiffAt (hU.mem_nhds hx.1)).mdifferentiableAt (by simp))
  have hvec (x : V) (hx : x ∈ O) (v : V) :
      chartVectorField p (fderiv ℝ ψ x v) (ρ x) = mfderiv 𝓘(ℝ, V) (𝓡 n) ρ x v := by
    rw [hderiv x hx]
    exact chartVectorField_differential p (ρ x) _ hx.2
  let T : Set ((ℝ × V) × V) := (Icc a b ×ˢ O) ×ˢ univ
  let C : Set ((ℝ × E) × E) := (Icc a b ×ˢ c.target) ×ˢ univ
  let P : (ℝ × V) × V → (ℝ × E) × E :=
    fun w => ((w.1.1, ψ w.1.2), fderiv ℝ ψ w.1.2 w.2)
  have hx : ContDiffOn ℝ ∞ (fun w : (ℝ × V) × V => w.1.2) T :=
    contDiff_fst.snd.contDiffOn
  have hP : ContDiffOn ℝ ∞ P T :=
    (contDiffOn_fst.fst.prodMk (hψ.comp hx (fun _ hw => hw.1.2))).prodMk
      ((hDψ.comp hx (fun _ hw => hw.1.2)).clm_apply contDiffOn_snd)
  have hPC : MapsTo P T C := fun w hw =>
    ⟨⟨hw.1.1, c.map_source hw.1.2.2⟩, mem_univ _⟩
  have hmetric : ContDiffOn ℝ ∞
      (fun w : (ℝ × E) × E => (F.metric w.1.1).pullbackCoefficients c.symm w.1.2 w.2 w.2)
      C :=
    (((chart_metric_coefficients_contDiffOn F p).comp contDiffOn_fst
      (fun _ hw => hw.1)).clm_apply contDiffOn_snd).clm_apply contDiffOn_snd
  have hm := hmetric.comp hP hPC
  have hh := (flow_hessian_chart_contDiffOn F hf p).comp hP hPC
  have hm' : ContDiffOn ℝ ∞
      (fun w : (ℝ × V) × V => (F.metric w.1.1).inner (ρ w.1.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)) T := by
    apply hm.congr
    intro w hw
    change (F.metric w.1.1).inner (ρ w.1.2) _ _ =
      (F.metric w.1.1).inner (c.symm (ψ w.1.2))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (ψ w.1.2) (fderiv ℝ ψ w.1.2 w.2))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (ψ w.1.2) (fderiv ℝ ψ w.1.2 w.2))
    erw [← chartVectorField_at_inverse p _ _ (c.map_source hw.1.2.2)]
    erw [show c.symm (ψ w.1.2) = ρ w.1.2 from c.left_inv hw.1.2.2,
      hvec w.1.2 hw.1.2 w.2]
  have hh' : ContDiffOn ℝ ∞
      (fun w : (ℝ × V) × V => (F.connection w.1.1).hessian f (ρ w.1.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ w.1.2 w.2)) T := by
    apply hh.congr
    intro w hw
    change (F.connection w.1.1).hessian f (ρ w.1.2) _ _ =
      (F.connection w.1.1).hessian f (c.symm (ψ w.1.2))
        (chartVectorField p (fderiv ℝ ψ w.1.2 w.2) (c.symm (ψ w.1.2)))
        (chartVectorField p (fderiv ℝ ψ w.1.2 w.2) (c.symm (ψ w.1.2)))
    rw [show c.symm (ψ w.1.2) = ρ w.1.2 from c.left_inv hw.1.2.2,
      hvec w.1.2 hw.1.2 w.2]
  have hTS : T ∈ 𝓝[S] z := by
    have hpre : {w : (ℝ × V) × V | w.1.2 ∈ O} ∈ 𝓝 z :=
      (continuous_fst.snd.continuousAt).preimage_mem_nhds (hO.mem_nhds hzO)
    filter_upwards [self_mem_nhdsWithin (s := S) (a := z),
      mem_nhdsWithin_of_mem_nhds hpre] with w hw hwo
    exact ⟨⟨hw.1.1, hwo⟩, mem_univ _⟩
  exact ⟨(hm' z ⟨⟨hz.1.1, hzO⟩, mem_univ _⟩).mono_of_mem_nhdsWithin hTS,
    (hh' z ⟨⟨hz.1.1, hzO⟩, mem_univ _⟩).mono_of_mem_nhdsWithin hTS⟩

end PoincareConjecture.M63
