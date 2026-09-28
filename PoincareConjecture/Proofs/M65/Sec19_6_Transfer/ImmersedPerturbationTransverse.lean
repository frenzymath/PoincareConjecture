import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationRegularBlocks
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationSiteCompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

local notation "ang" => (fun x : ℝ =>
  (Subtype.mk (Proofs.M58.angularPoint x) (Proofs.M58.norm_angularPoint x) : LoopCircle))

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

def loopDoublePointEquation (Gamma : P → ℝ → C1FreeLoopSpace (M := M))
    (q : M) (w : P × LoopAmbient) : LoopAmbient :=
  (chartAt LoopAmbient q) (periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 0)) -
    (chartAt LoopAmbient q) (periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 1))

theorem loopDoublePointEquation_contDiffAt
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (J : Set ℝ) (d : ℝ) (hJ : IsOpen J)
    (hGamma : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞
      (fun w => periodicFreeLoop (Gamma w.1 w.2.2) w.2.1) (ball 0 d ×ˢ (univ ×ˢ J)))
    (q : M) (w : P × LoopAmbient) (hp : w.1 ∈ ball 0 d) (ht : w.2 2 ∈ J)
    (hx : periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 0) ∈ (chartAt LoopAmbient q).source)
    (hy : periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 1) ∈ (chartAt LoopAmbient q).source) :
    ContDiffAt ℝ ∞ (loopDoublePointEquation Gamma q) w := by
  have hpart (i : Fin 3)
      (hi : periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 i) ∈ (chartAt LoopAmbient q).source) :
      ContDiffAt ℝ ∞ (fun z : P × LoopAmbient =>
        (chartAt LoopAmbient q) (periodicFreeLoop (Gamma z.1 (z.2 2)) (z.2 i))) w :=
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hi).comp w
      (site_value_contMDiffAt Gamma J d hJ hGamma w hp ht i)).contDiffAt
  exact (hpart 0 hx).sub (hpart 1 hy)

variable [T2Space M] [CompactSpace M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {J : Set ℝ}

set_option maxHeartbeats 1400000 in

theorem exists_transverse_control_family (C : M65SmoothFilledLoopFamily F J)
    (hJ : IsOpen J) (K : Set ℝ) (hK : IsCompact K) (hKJ : K ⊆ J)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ (k : ℕ) (d : ℝ) (Gamma : (Fin (k * 3) → ℝ) → ℝ → C1FreeLoopSpace (M := M))
        (q : Fin k → M) (O : Set ((Fin (k * 3) → ℝ) × LoopAmbient)),
      0 < d ∧ IsOpen O ∧
      ContMDiffOn 𝓘(ℝ, (Fin (k * 3) → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
        (fun w => periodicFreeLoop (Gamma w.1 w.2.2) w.2.1) (ball 0 d ×ˢ (univ ×ˢ J)) ∧
      (∀ t ∈ J, ∀ x, periodicFreeLoop (Gamma 0 t) x = periodicFreeLoop (C.loops t) x) ∧
      (∀ z : LoopAmbient, z 2 ∈ K → rho ≤ dist (ang (z 0)) (ang (z 1)) →
        periodicFreeLoop (C.loops (z 2)) (z 0) = periodicFreeLoop (C.loops (z 2)) (z 1) →
          (0, z) ∈ O) ∧
      ∀ w ∈ O, ∃ i : Fin k,
        ContDiffAt ℝ 1 (loopDoublePointEquation Gamma (q i)) w ∧
        Function.Bijective ((fderiv ℝ (fun p => loopDoublePointEquation Gamma (q i) (p, w.2))
          w.1).comp (controlBlock i)) := by
  classical
  obtain ⟨k, d, beta, Phi, q, U, hd, hbeta, hbound, hPhi, hzero, _hU, hsource, _hQU, hBU,
      hcover⟩ := exists_finite_regular_controls C hJ K hK hKJ rho hrho
  obtain ⟨delta, Gamma, hdelta, _hle, hGammaValue, hGamma, hbase⟩ :=
    exists_combined_control_family C d hd beta hbeta hbound Phi hPhi hzero
  let allPhi : Fin (k * 3) → M × ℝ → M :=
    fun j => Phi (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  let allBeta : Fin (k * 3) → LoopPlane → ℝ := fun j => beta (finProdFinEquiv.symm j).1
  let D : Set LoopAmbient := {z | z 2 ∈ K ∧ rho ≤ dist (ang (z 0)) (ang (z 1)) ∧
    periodicFreeLoop (C.loops (z 2)) (z 0) = periodicFreeLoop (C.loops (z 2)) (z 1)}
  have hlocal (z : D) : ∃ (i : Fin k) (V : Set ((Fin (k * 3) → ℝ) × LoopAmbient)),
      IsOpen V ∧ (0, z.1) ∈ V ∧ ContDiffOn ℝ 1 (loopDoublePointEquation Gamma (q i)) V ∧
      ∀ w ∈ V, Function.Bijective
        ((fderiv ℝ (fun p => loopDoublePointEquation Gamma (q i) (p, w.2)) w.1).comp
          (controlBlock i)) := by
    have hcircle : C.loops (z.1 2) (ang (z.1 0)) = C.loops (z.1 2) (ang (z.1 1)) :=
      ((C.loops (z.1 2)).boundary (ang (z.1 0))).symm.trans
        (z.2.2.2.trans ((C.loops (z.1 2)).boundary (ang (z.1 1))))
    obtain ⟨i, v, hv, hsite⟩ := hcover (loopSite z.1) z.2.1 z.2.2.1 hcircle
    have hsites : loopSite z.1 = loopSite v := hsite.symm
    obtain ⟨_ht, hcx, hcy⟩ := original_values_eq_of_loopSite C z.1 v hsites
    obtain ⟨_htv, hxv, hyv⟩ := hsource i (0, v) hv
    have hx : periodicFreeLoop (C.loops (z.1 2)) (z.1 0) ∈ (chartAt LoopAmbient (q i)).source :=
      hcx ▸ hxv
    have hy : periodicFreeLoop (C.loops (z.1 2)) (z.1 1) ∈ (chartAt LoopAmbient (q i)).source :=
      hcy ▸ hyv
    have hlocalEq : (fun p => doublePointEquation C (Phi i)
        (fun _ x => beta i (Proofs.M58.angularPoint x)) (List.finRange 3) (q i) (p, z.1)) =
        (fun p => doublePointEquation C (Phi i)
        (fun _ x => beta i (Proofs.M58.angularPoint x)) (List.finRange 3) (q i) (p, v)) :=
      funext (doublePointEquation_eq_of_loopSite C (Phi i) (fun _ => beta i)
        (List.finRange 3) (q i) z.1 v hsites)
    have hfull : Function.Bijective ((fderiv ℝ (fun p => doublePointEquation C allPhi
        (fun j x => allBeta j (Proofs.M58.angularPoint x)) (List.finRange (k * 3)) (q i)
          (p, z.1)) 0).comp (controlBlock i)) := by
      rw [combined_control_block_eq C d hd beta hbeta hbound Phi hPhi hzero i (q i) z.1 hx hy,
        hlocalEq]
      exact hBU i (0, v) hv
    have hparameter : (fun p => loopDoublePointEquation Gamma (q i) (p, z.1)) =ᶠ[𝓝 0]
        (fun p => doublePointEquation C allPhi
          (fun j x => allBeta j (Proofs.M58.angularPoint x))
          (List.finRange (k * 3)) (q i) (p, z.1)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin (k * 3) → ℝ) hdelta] with p hp
      simp only [loopDoublePointEquation, doublePointEquation,
        hGammaValue p hp (z.1 2) (hKJ z.2.1), allPhi, allBeta]
    have hblock : Function.Bijective
        ((fderiv ℝ (fun p => loopDoublePointEquation Gamma (q i) (p, z.1)) 0).comp
          (controlBlock i)) := by
      rw [hparameter.fderiv_eq]
      exact hfull
    have hxG : periodicFreeLoop (Gamma 0 (z.1 2)) (z.1 0) ∈ (chartAt LoopAmbient (q i)).source := by
      rw [hbase (z.1 2) (hKJ z.2.1)]
      exact hx
    have hyG : periodicFreeLoop (Gamma 0 (z.1 2)) (z.1 1) ∈ (chartAt LoopAmbient (q i)).source := by
      rw [hbase (z.1 2) (hKJ z.2.1)]
      exact hy
    have hQ := loopDoublePointEquation_contDiffAt Gamma J delta hJ hGamma (q i) (0, z.1)
      (mem_ball_self hdelta) (hKJ z.2.1) hxG hyG
    obtain ⟨V, hV, hzV, hQV, hBV⟩ := exists_selected_block_neighborhood i
      (loopDoublePointEquation Gamma (q i)) (0, z.1) (hQ.of_le (by simp)) hblock
    exact ⟨i, V, hV, hzV, hQV, hBV⟩
  choose i V hV hzV hQV hBV using hlocal
  refine ⟨k, delta, Gamma, q, ⋃ z : D, V z, hdelta, isOpen_iUnion hV, hGamma, hbase, ?_, ?_⟩
  · intro z ht hsep heq
    exact mem_iUnion.mpr ⟨⟨z, ht, hsep, heq⟩, hzV ⟨z, ht, hsep, heq⟩⟩
  · intro w hw
    obtain ⟨z, hz⟩ := mem_iUnion.mp hw
    exact ⟨i z, (hQV z).contDiffAt ((hV z).mem_nhds hz), hBV z w hz⟩

end PoincareConjecture.M65Perturbation
