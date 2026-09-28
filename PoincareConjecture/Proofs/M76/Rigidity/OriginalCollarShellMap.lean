import PoincareConjecture.Proofs.M76.Rigidity.CollarCoreBoundaryParameter
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnitCubePLCollar

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V3) 1
local notation "J" => Icc (0 : ℝ) (1 / 8)
local notation "I" => Icc (0 : ℝ) 1
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3}

theorem exists_original_collar_shell_map
    (L : SimplicialComplex ℝ E) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (qH : Q ≃ₜ L.space) (hqH : qH.IsFinitePL)
    (h : (Q ×ˢ J : Set (V3 × ℝ)) ≃ₜ T) (hh : h.IsFinitePL)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ f : V3 → X, PolyhedralPLInCharts e f T ∧ InjOn f T ∧
      f '' T = c '' (L.space ×ˢ Icc 0 ε) ∧
      ∀ z : (Q ×ˢ J : Set (V3 × ℝ)),
        f (h z) = c ((qH ⟨(z : V3 × ℝ).1, z.property.1⟩ : E),
          8 * ε * (z : V3 × ℝ).2) := by
  obtain ⟨q, hq, hqval⟩ := hqH
  obtain ⟨g, hg, hgval⟩ := hh.symm
  have hgm : MapsTo g T (Q ×ˢ J) := by
    intro x hx
    rw [← hgval ⟨x, hx⟩]
    exact (h.symm ⟨x, hx⟩).property
  have hginj : InjOn g T := by
    intro x hx y hy hxy
    rw [← hgval ⟨x, hx⟩, ← hgval ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (h.symm.injective (Subtype.ext hxy))
  have hgh (z : (Q ×ˢ J : Set (V3 × ℝ))) : g (h z) = (z : V3 × ℝ) := by
    rw [← hgval (h z), h.symm_apply_apply]
  have hscale : 0 < 8 * ε := by positivity
  let A : ℝ →ᴬ[ℝ] ℝ := ((8 * ε) • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨M, hM, hMJ, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 / 8 by norm_num)
  have hA : FinitePiecewiseAffineOn (fun t : ℝ => 8 * ε * t) J :=
    ⟨M, hM, hMJ, M.affineOnFaces_affine A⟩
  let ψ : V3 × ℝ → E × ℝ := Prod.map q (fun t => 8 * ε * t)
  have hψ : FinitePiecewiseAffineOn ψ (Q ×ˢ J) := hq.prodMap hA
  have hψm : MapsTo ψ (Q ×ˢ J) (L.space ×ˢ Icc 0 ε) := by
    intro z hz
    have hbase : q z.1 ∈ L.space := by
      rw [← hqval ⟨z.1, hz.1⟩]
      exact (qH ⟨z.1, hz.1⟩).property
    refine ⟨hbase, mul_nonneg hscale.le hz.2.1, ?_⟩
    change 8 * ε * z.2 ≤ ε
    nlinarith [hz.2.2]
  have hsub : L.space ×ˢ Icc (0 : ℝ) ε ⊆ L.space ×ˢ I :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans hε1⟩
  have hψinj : InjOn ψ (Q ×ˢ J) := by
    intro z hz w hw hzw
    have hfirst : q z.1 = q w.1 := congrArg (fun v : E × ℝ => v.1) hzw
    rw [← hqval ⟨z.1, hz.1⟩, ← hqval ⟨w.1, hw.1⟩] at hfirst
    have hfst : z.1 = w.1 := congrArg Subtype.val (qH.injective (Subtype.ext hfirst))
    have htime : 8 * ε * z.2 = 8 * ε * w.2 :=
      congrArg (fun v : E × ℝ => v.2) hzw
    exact Prod.ext hfst (mul_left_cancel₀ hscale.ne' htime)
  have hcInj : InjOn c (L.space ×ˢ I) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw)
  let f : V3 → X := c ∘ ψ ∘ g
  have hψg : FinitePiecewiseAffineOn (ψ ∘ g) T := hψ.comp hg hgm
  obtain ⟨K, hK, hKT, _⟩ := hg
  have hf : PolyhedralPLInCharts e f T := by
    have hPL := hc.comp_finitePiecewiseAffineOn K hK (hKT.symm ▸ hψg)
      (fun _ hx => hsub (hψm (hgm (hKT.subset hx))))
    exact hKT ▸ hPL
  have hfi : InjOn f T := by
    intro x hx y hy hxy
    apply hginj hx hy
    apply hψinj (hgm hx) (hgm hy)
    exact hcInj (hsub (hψm (hgm hx))) (hsub (hψm (hgm hy))) hxy
  have hvalue (z : (Q ×ˢ J : Set (V3 × ℝ))) :
      f (h z) = c ((qH ⟨(z : V3 × ℝ).1, z.property.1⟩ : E),
        8 * ε * (z : V3 × ℝ).2) := by
    change c (ψ (g (h z))) = _
    rw [hgh]
    change c (q (z : V3 × ℝ).1, 8 * ε * (z : V3 × ℝ).2) = _
    rw [← hqval ⟨(z : V3 × ℝ).1, z.property.1⟩]
  refine ⟨f, hf, hfi, ?_, hvalue⟩
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨ψ (g z), hψm (hgm hz), rfl⟩
  · rintro x ⟨w, hw, rfl⟩
    let z0 : Q := qH.symm ⟨w.1, hw.1⟩
    have ht : w.2 / (8 * ε) ∈ J := by
      refine ⟨div_nonneg hw.2.1 hscale.le, (div_le_iff₀ hscale).mpr ?_⟩
      nlinarith [hw.2.2]
    let z : (Q ×ˢ J : Set (V3 × ℝ)) := ⟨((z0 : V3), w.2 / (8 * ε)), z0.property, ht⟩
    refine ⟨h z, (h z).property, ?_⟩
    rw [hvalue]
    change c ((qH (qH.symm ⟨w.1, hw.1⟩) : E), 8 * ε * (w.2 / (8 * ε))) = c w
    rw [qH.apply_symm_apply]
    have htime : 8 * ε * (w.2 / (8 * ε)) = w.2 := by
      field_simp [hε.ne']
    rw [htime]

end PoincareConjecture.M76
