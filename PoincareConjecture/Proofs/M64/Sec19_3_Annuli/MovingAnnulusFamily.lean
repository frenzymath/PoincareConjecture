import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.SmoothAnnulusAdmission
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}






theorem m64Annulus_exists_smooth_moving_boundary_family
    (A : M64Annulus g c0 c1) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (f0 f1 : ℝ → ℝ → M)
    (hf0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q => f0 q.1 q.2) (Ioo (-epsilon) epsilon ×ˢ univ))
    (hf1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q => f1 q.1 q.2) (Ioo (-epsilon) epsilon ×ˢ univ))
    (hinit0 : ∀ x, f0 0 x = c0 x) (hinit1 : ∀ x, f1 0 x = c1 x)
    (hper0 : ∀ r x, f0 r (x + curvePeriod) = f0 r x)
    (hper1 : ∀ r x, f1 r (x + curvePeriod) = f1 r x) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ U : Set LoopPlane, IsOpen U ∧
      m64AnnulusDomain ⊆ U ∧ ∃ v : ℝ × LoopPlane → M,
      ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
        (Ioo (-delta) delta ×ˢ U) ∧
      (∀ p, v (0, p) = A.map p) ∧
      (∀ r x s, v (r, annulusPoint (x + curvePeriod) s) =
        v (r, annulusPoint x s)) ∧
      (∀ r x, v (r, annulusPoint x 0) = f0 r x) ∧
      (∀ r x, v (r, annulusPoint x 1) = f1 r x) ∧
      ∀ r ∈ Ioo (-delta) delta, ∀ g' : RiemannianMetric n M,
        ∃ B : M64Annulus g' (f0 r) (f1 r), B.map = fun p => v (r, p) := by
  let : Nonempty M := ⟨A.map 0⟩
  obtain ⟨d, e, he, hemb, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨V, rho, hV, heV, hrho, hrhoe, _, _⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  let W : ℝ × LoopPlane → EuclideanSpace ℝ (Fin d) := fun q =>
    e (A.map q.2) + (1 - q.2 1) • (e (f0 q.1 (q.2 0)) - e (f0 0 (q.2 0))) +
      q.2 1 • (e (f1 q.1 (q.2 0)) - e (f1 0 (q.2 0)))
  let v : ℝ × LoopPlane → M := rho ∘ W
  let Omega : Set (ℝ × LoopPlane) := Ioo (-epsilon) epsilon ×ˢ O
  have hOmega : IsOpen Omega := isOpen_Ioo.prod hO
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hcoord (i : Fin 2) : ContDiff ℝ ∞ (fun q : ℝ × LoopPlane => q.2 i) := by
    fun_prop
  have hpair : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : ℝ × LoopPlane => (q.1, q.2 0)) :=
    (contDiff_fst.prodMk (hcoord 0)).contMDiff
  have hpair0 : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : ℝ × LoopPlane => ((0 : ℝ), q.2 0)) :=
    ((contDiff_const (c := (0 : ℝ))).prodMk (hcoord 0)).contMDiff
  have hmaps : MapsTo (fun q : ℝ × LoopPlane => (q.1, q.2 0)) Omega
      (Ioo (-epsilon) epsilon ×ˢ univ) := fun _ hq => ⟨hq.1, mem_univ _⟩
  have hmaps0 : MapsTo (fun q : ℝ × LoopPlane => (0, q.2 0)) Omega
      (Ioo (-epsilon) epsilon ×ˢ univ) := fun _ _ => ⟨hzero, mem_univ _⟩
  have hEA : ContDiffOn ℝ ∞ (fun q : ℝ × LoopPlane => e (A.map q.2)) Omega :=
    (he.comp_contMDiffOn (hA.comp contDiff_snd.contMDiff.contMDiffOn
      (fun _ hq => hq.2))).contDiffOn
  have hF0 : ContDiffOn ℝ ∞ (fun q : ℝ × LoopPlane => e (f0 q.1 (q.2 0))) Omega :=
    (he.comp_contMDiffOn (hf0.comp hpair.contMDiffOn hmaps)).contDiffOn
  have hF1 : ContDiffOn ℝ ∞ (fun q : ℝ × LoopPlane => e (f1 q.1 (q.2 0))) Omega :=
    (he.comp_contMDiffOn (hf1.comp hpair.contMDiffOn hmaps)).contDiffOn
  have hF00 : ContDiffOn ℝ ∞ (fun q : ℝ × LoopPlane => e (f0 0 (q.2 0))) Omega :=
    (he.comp_contMDiffOn (hf0.comp hpair0.contMDiffOn hmaps0)).contDiffOn
  have hF10 : ContDiffOn ℝ ∞ (fun q : ℝ × LoopPlane => e (f1 0 (q.2 0))) Omega :=
    (he.comp_contMDiffOn (hf1.comp hpair0.contMDiffOn hmaps0)).contDiffOn
  have hW : ContDiffOn ℝ ∞ W Omega :=
    (hEA.add ((contDiffOn_const.sub (hcoord 1).contDiffOn).smul (hF0.sub hF00))).add
      ((hcoord 1).contDiffOn.smul (hF1.sub hF10))
  have hWzero (p : LoopPlane) : W (0, p) = e (A.map p) := by
    simp only [W, sub_self, smul_zero, add_zero]
  have hbase (p : LoopPlane) : v (0, p) = A.map p := by
    change rho (W (0, p)) = A.map p
    rw [hWzero, hrhoe]
  have hopen : IsOpen (Omega ∩ W ⁻¹' V) :=
    hW.continuousOn.isOpen_inter_preimage hOmega hV
  have htube : ({0} : Set ℝ) ×ˢ m64AnnulusDomain ⊆ Omega ∩ W ⁻¹' V := by
    rintro ⟨r, p⟩ ⟨hr, hp⟩
    rcases mem_singleton_iff.mp hr with rfl
    exact ⟨⟨hzero, hdom hp⟩, by rw [mem_preimage, hWzero]; exact heV (mem_range_self _)⟩
  obtain ⟨J, U, hJ, hU, hJU, hDU, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton m64AnnulusDomain_isCompact hopen htube
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (hJU (mem_singleton 0)))
  have hsmall : Ioo (-delta) delta ⊆ J := by
    intro r hr
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr
  have hsubset : Ioo (-delta) delta ×ˢ U ⊆ Omega ∩ W ⁻¹' V :=
    (prod_mono_left hsmall).trans hprod
  have hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-delta) delta ×ˢ U) :=
    hrho.comp (hW.mono (hsubset.trans inter_subset_left)).contMDiffOn
      (fun _ hq => (hsubset hq).2)
  have hperiodic (r x s : ℝ) : v (r, annulusPoint (x + curvePeriod) s) =
      v (r, annulusPoint x s) := by
    change rho (e (A.map (annulusPoint (x + curvePeriod) s)) +
      (1 - s) • (e (f0 r (x + curvePeriod)) - e (f0 0 (x + curvePeriod))) +
      s • (e (f1 r (x + curvePeriod)) - e (f1 0 (x + curvePeriod)))) =
      rho (e (A.map (annulusPoint x s)) +
        (1 - s) • (e (f0 r x) - e (f0 0 x)) + s • (e (f1 r x) - e (f1 0 x)))
    rw [A.periodic, hper0, hper0, hper1, hper1]
  have hlower (r x : ℝ) : v (r, annulusPoint x 0) = f0 r x := by
    change rho (W (r, annulusPoint x 0)) = f0 r x
    have hw : W (r, annulusPoint x 0) = e (f0 r x) := by
      change e (A.map (annulusPoint x 0)) +
        (1 - (0 : ℝ)) • (e (f0 r x) - e (f0 0 x)) +
        (0 : ℝ) • (e (f1 r x) - e (f1 0 x)) = e (f0 r x)
      rw [A.lower_boundary, hinit0]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      abel
    rw [hw, hrhoe]
  have hupper (r x : ℝ) : v (r, annulusPoint x 1) = f1 r x := by
    change rho (W (r, annulusPoint x 1)) = f1 r x
    have hw : W (r, annulusPoint x 1) = e (f1 r x) := by
      change e (A.map (annulusPoint x 1)) +
        (1 - (1 : ℝ)) • (e (f0 r x) - e (f0 0 x)) +
        (1 : ℝ) • (e (f1 r x) - e (f1 0 x)) = e (f1 r x)
      rw [A.upper_boundary, hinit1]
      simp only [sub_self, one_smul, zero_smul, add_zero]
      abel
    rw [hw, hrhoe]
  refine ⟨delta, hdelta, U, hU, hDU, v, hv, hbase, hperiodic, hlower, hupper, ?_⟩
  intro r hr g'
  have hslice : ContMDiffOn (𝓡 2) (𝓡 n) 1 (fun p => v (r, p)) U :=
    (hv.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      (fun _ hp => ⟨hr, hp⟩)).of_le (by simp)
  exact m64Annulus_exists_eq_of_contMDiffOn g' hU hDU hslice
    (hperiodic r) (hlower r) (hupper r)

end PoincareConjecture
