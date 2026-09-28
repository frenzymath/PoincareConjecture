import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawTimePrincipal
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawLowerComponents
import PoincareConjecture.Proofs.M04.FlowTensorRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem raw_family_spatial_fderiv_contDiffOn
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {J : Set ℝ} {f : ℝ → V → W}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => fderiv ℝ (f p.1) p.2) (J ×ˢ univ) := by
  intro p hp
  have hmap : MapsTo (fun q : (ℝ × V) × V => (q.1.1, q.2))
      ((J ×ˢ univ) ×ˢ univ) (J ×ˢ univ) := fun _ hq => ⟨hq.1.1, mem_univ _⟩
  have hf' : ContDiffWithinAt ℝ ∞ (fun q : (ℝ × V) × V => f q.1.1 q.2)
      ((J ×ˢ univ) ×ˢ univ) (p, p.2) :=
    (hf p hp).comp (p, p.2)
      (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd)
      hmap
  simpa only [fderivWithin_univ] using
    hf'.fderivWithin contDiffWithinAt_snd uniqueDiffOn_univ
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp) hp (fun _ _ => mem_univ _)

theorem raw_metric_pair_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (u v : V) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => (F.metric p.1).inner p.2 u v) (J ×ˢ univ) := by
  have hu := euclidean_field_contMDiff
    (contDiff_const (c := u) : ContDiff ℝ ∞ (fun _ : V => u))
  have hv := euclidean_field_contMDiff
    (contDiff_const (c := v) : ContDiff ℝ ∞ (fun _ : V => v))
  have h := Proofs.M03.contMDiffOn_family_metric_pair (U := univ) F.smooth _ _
    hu.contMDiffOn hv.contMDiffOn
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffOn

theorem raw_connection_pair_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (u v : V) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => rawConnectionCoefficient (F.connection p.1) p.2 u v)
      (J ×ˢ univ) := by
  have hu := euclidean_field_contMDiff
    (contDiff_const (c := u) : ContDiff ℝ ∞ (fun _ : V => u))
  have hv := euclidean_field_contMDiff
    (contDiff_const (c := v) : ContDiff ℝ ∞ (fun _ : V => v))
  have h := Proofs.M03.contMDiffOn_connection_family_apply F.smooth F.connection
    isOpen_univ (fun _ : V => v) (fun _ : V => u) hv.contMDiffOn hu.contMDiffOn
  have h' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × V => rawConnectionCoefficient (F.connection p.1) p.2 u v)
      (J ×ˢ univ) := by
    intro p hp
    simpa only [trivializationAt_model_space_apply] using!
      (Bundle.contMDiffWithinAt_totalSpace.mp (h p hp)).2
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h'
  exact h'.contDiffOn

theorem rawConnectionCoefficient_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawConnectionCoefficient (F.connection p.1) p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  exact raw_connection_pair_family_contDiffOn F u v

theorem rawConnectionDerivative_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V =>
      fderiv ℝ (rawConnectionCoefficient (F.connection p.1)) p.2) (J ×ˢ univ) :=
  raw_family_spatial_fderiv_contDiffOn
    (f := fun t => rawConnectionCoefficient (F.connection t))
    (rawConnectionCoefficient_family_contDiffOn F)

theorem raw_ricci_pair_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (u v : V) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => (F.connection p.1).ricci p.2 u v) (J ×ˢ univ) := by
  let X : Fin 2 → V → V := ![fun _ => u, fun _ => v]
  have hX (i : Fin 2) : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x => Bundle.TotalSpace.mk' V x (E := TangentSpace (𝓡 n)) (X i x)) univ := by
    fin_cases i
    · exact (euclidean_field_contMDiff (contDiff_const (c := u))).contMDiffOn
    · exact (euclidean_field_contMDiff (contDiff_const (c := v))).contMDiffOn
  have h := M04.contMDiffOn_flow_ricciEvaluation F isOpen_univ hX
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffOn

end PoincareConjecture.M35.Uniqueness.Heat
