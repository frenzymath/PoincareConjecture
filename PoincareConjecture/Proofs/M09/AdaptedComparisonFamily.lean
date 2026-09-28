import PoincareConjecture.Proofs.M09.FiniteFieldSum
import PoincareConjecture.Proofs.M09.CompactFieldVariation
import PoincareConjecture.Proofs.M09.AdaptedOrthonormalFrame
import PoincareConjecture.Proofs.M09.VelocityChainRules








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => Fin n → ℝ

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_scaled_frame_comparison_family {J : Set ℝ} (F : RicciFlow n M J)
    (T c : ℝ) (hc : 0 < c) (α : ℝ → M)
    (P : Fin n → ∀ s, TangentSpace (𝓡 n) (α s))
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hP : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, P i s⟩ : TangentBundle (𝓡 n) M)) U)
    (hpair : ∀ i j, (F.metric (T - c ^ 2)).inner (α c) (P i c) (P j c) =
      if i = j then 1 else 0) :
    ∃ (f : V × ℝ → M) (Ω : Set (V × ℝ)) (N : Set V),
      IsOpen Ω ∧ IsOpen N ∧ (0 : V) ∈ N ∧ N ×ˢ Set.Icc 0 c ⊆ Ω ∧
      ContMDiffOn (𝓘(ℝ, V × ℝ)) (𝓡 n) ∞ f Ω ∧
      (∀ s, f (0, s) = α s) ∧ (∀ x, f (x, 0) = α 0) ∧
      (∀ s ∈ Set.Icc 0 c, ∀ x : V,
        (curveVelocity (n := n) (fun r : ℝ ↦ f (r • x, s)) 0 : E) =
          ∑ i, x i • ((s / c) • P i s)) ∧
      Function.Bijective (mfderiv (𝓘(ℝ, V)) (𝓡 n) (fun x ↦ f (x, c)) 0) := by
  classical
  let Y : ∀ s, V →L[ℝ] TangentSpace (𝓡 n) (α s) := fun s ↦
    ∑ i : Fin n, (ContinuousLinearMap.toSpanSingleton ℝ ((s / c) • P i s)).comp
      (ContinuousLinearMap.proj i)
  have hYval (s : ℝ) (x : V) : Y s x = ∑ i, x i • ((s / c) • P i s) := by
    simp only [Y, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply]
  have hY (x : V) : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, Y s x⟩ : TangentBundle (𝓡 n) M)) U := by
    have hi (i : Fin n) : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun s ↦ (⟨α s, x i • ((s / c) • P i s)⟩ : TangentBundle (𝓡 n) M)) U := by
      simpa only [smul_smul] using field_smul_smooth α (P i) (fun s ↦ x i * (s / c))
        U hU hα (contDiffOn_const.mul (contDiffOn_id.div_const c)) (hP i)
    simpa only [hYval] using field_sum_smooth α (fun i s ↦ x i • ((s / c) • P i s))
      U hU hα hi
  obtain ⟨g, W, N, hW, hN, h0N, hKN, hg, hcenter, hfixed, hvelocity⟩ :=
    exists_smooth_family_of_compact_linear_field α Y U (Set.Icc 0 c)
      hU isCompact_Icc hKU hα hY
  let f : V × ℝ → M := fun z ↦ g (z.2, z.1)
  let Ω : Set (V × ℝ) := Prod.swap ⁻¹' W
  have hΩ : IsOpen Ω := hW.preimage continuous_swap
  have hf : ContMDiffOn (𝓘(ℝ, V × ℝ)) (𝓡 n) ∞ f Ω :=
    hg.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn (fun _ hz ↦ hz)
  have hNΩ : N ×ˢ Set.Icc 0 c ⊆ Ω := fun z hz ↦ hKN ⟨hz.2, hz.1⟩
  have hYzero : Y 0 = 0 := by
    ext x
    simp only [hYval, zero_div, zero_smul, smul_zero, Finset.sum_const_zero,
      ContinuousLinearMap.zero_apply]
  refine ⟨f, Ω, N, hΩ, hN, h0N, hNΩ, hf, hcenter,
    (fun x ↦ hfixed 0 hYzero x), (fun s hs x ↦ (hvelocity s hs x).trans (hYval s x)), ?_⟩
  have hcK : c ∈ Set.Icc 0 c := ⟨hc.le, le_rfl⟩
  have hfc : ContMDiffAt (𝓘(ℝ, V)) (𝓡 n) ∞ (fun x ↦ f (x, c)) 0 :=
    (hf.contMDiffAt (hΩ.mem_nhds (hNΩ ⟨h0N, hcK⟩))).comp 0
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hder (x : V) :
      (mfderiv (𝓘(ℝ, V)) (𝓡 n) (fun y ↦ f (y, c)) 0 x : E) = ∑ i, x i • P i c := by
    have hchain := curveVelocity_comp_initial_line (fun y ↦ f (y, c)) 0 x
      (hfc.mdifferentiableAt (by simp))
    have hcurve : (fun r : ℝ ↦ f (0 + r • x, c)) = (fun r ↦ g (c, r • x)) := by
      funext r
      change g (c, 0 + r • x) = g (c, r • x)
      rw [zero_add]
    have hcv := congrArg (fun γ : ℝ → M ↦ (curveVelocity γ 0 : E)) hcurve
    have hv := (hvelocity c hcK x).trans (hYval c x)
    simpa only [div_self hc.ne', one_smul] using hchain.symm.trans (hcv.trans hv)
  have hbase : f (0, c) = α c := hcenter c
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - c ^ 2)).toRiemannianMetric⟩
  have hterminalPair (i j : Fin n) :
      (F.metric (T - c ^ 2)).inner (f (0, c)) (P i c) (P j c) =
        if i = j then 1 else 0 := by
    rw [hbase]
    exact hpair i j
  obtain ⟨e, he⟩ := exists_orthonormalBasis_of_metric_pairing
    (F.metric (T - c ^ 2)) (f (0, c)) (fun i ↦ P i c) hterminalPair
  have hmap : (fun x : V ↦ (mfderiv (𝓘(ℝ, V)) (𝓡 n) (fun y ↦ f (y, c)) 0 x : E)) =
      (fun x : V ↦ (e.toBasis.equivFun.symm x : E)) := by
    funext x
    rw [hder, e.toBasis.equivFun_symm_apply]
    exact Finset.sum_congr rfl (fun i _ ↦ congrArg (fun v : E ↦ x i • v) (he i).symm)
  change Function.Bijective (fun x : V ↦
    (mfderiv (𝓘(ℝ, V)) (𝓡 n) (fun y ↦ f (y, c)) 0 x : E))
  rw [hmap]
  exact e.toBasis.equivFun.symm.bijective

end PoincareConjecture.Proofs.M09
