import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapDistance
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35

private theorem first_exit_compact {X : Type*} [TopologicalSpace X]
    {U K : Set X} (hU : IsOpen U) (hK : IsClosed K) (hUK : U ⊆ K)
    (gamma : ℝ → X) (hgamma : ContinuousOn gamma (Icc 0 1))
    (hzero : gamma 0 ∈ U) (hone : gamma 1 ∉ U) :
    ∃ t ∈ Ioc (0 : ℝ) 1, MapsTo gamma (Icc 0 t) K ∧ gamma t ∉ U := by
  let T := Icc (0 : ℝ) 1 ∩ gamma ⁻¹' Uᶜ
  have hT : IsCompact T := isCompact_Icc.of_isClosed_subset
    (hgamma.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl) inter_subset_left
  obtain ⟨t, ht, hmin⟩ := hT.exists_isMinOn
    ⟨1, ⟨⟨by norm_num, le_rfl⟩, hone⟩⟩ continuousOn_id
  have htpos : 0 < t := by
    by_contra h
    have heq : t = 0 := le_antisymm (le_of_not_gt h) ht.1.1
    exact ht.2 (heq ▸ hzero)
  have hbefore : MapsTo gamma (Ico 0 t) U := by
    intro s hs
    by_contra hout
    exact (not_lt_of_ge (hmin ⟨⟨hs.1, hs.2.le.trans ht.1.2⟩, hout⟩)) hs.2
  have hendK : gamma t ∈ K := by
    have hc : ContinuousWithinAt gamma (Ico 0 t) t :=
      (hgamma t ht.1).mono (fun s hs => ⟨hs.1, hs.2.le.trans ht.1.2⟩)
    have hcl : t ∈ closure (Ico 0 t) := by
      rw [closure_Ico htpos.ne]
      exact ⟨htpos.le, le_rfl⟩
    exact hK.closure_eq ▸ hc.mem_closure hcl (fun _ hs => hUK (hbefore hs))
  refine ⟨t, ⟨htpos, ht.1.2⟩, ?_, ht.2⟩
  intro s hs
  rcases hs.2.eq_or_lt with rfl | hst
  · exact hendK
  · exact hUK (hbefore ⟨hs.1, hst⟩)

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

theorem inverse_tangentNorm_bound
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (A : ℝ)
    (hbound : ∀ x ∈ phi.source, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ A * h.tangentNorm (phi x) (mfderiv (𝓡 3) (𝓡 3) phi x v)) :
    ∀ y ∈ phi.target, ∀ v : TangentSpace (𝓡 3) y,
      g.tangentNorm (phi.invFun y) (mfderiv (𝓡 3) (𝓡 3) phi.invFun y v) ≤
        A * h.tangentNorm y v := by
  intro y hy v
  have hsource := phi.map_target hy
  have hi : MDifferentiableAt (𝓡 3) (𝓡 3) phi.invFun y :=
    phi.symm.mdifferentiableAt (by simp) hy
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3) phi (phi.invFun y) :=
    phi.mdifferentiableAt (by simp) hsource
  have heq : (phi ∘ phi.invFun) =ᶠ[𝓝 y] id :=
    Filter.eventuallyEq_of_mem (phi.open_target.mem_nhds hy) (fun _ hz => phi.right_inv hz)
  have hd : (mfderiv (𝓡 3) (𝓡 3) phi (phi.invFun y))
      (mfderiv (𝓡 3) (𝓡 3) phi.invFun y v) = v := by
    have h : mfderiv (𝓡 3) (𝓡 3) (phi ∘ phi.invFun) y =
        mfderiv (𝓡 3) (𝓡 3) (id : N → N) y := heq.mfderiv_eq
    rw [mfderiv_comp y hf hi, mfderiv_id] at h
    exact congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => B v) h
  have hnorm := congrArg₂ (fun z : N => fun w : EuclideanSpace ℝ (Fin 3) => h.tangentNorm z w)
    (phi.right_inv hy) hd
  exact (hbound (phi.invFun y) hsource _).trans_eq (congrArg (fun z : ℝ => A * z) hnorm)

theorem ball_subset_image_of_tangentNorm_lower [T3Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) {A r : ℝ}
    (hA : 0 < A) (hr : 0 < r) (x : M)
    (hcompact : IsCompact (closure (g.ball x r)))
    (hsource : closure (g.ball x r) ⊆ phi.source)
    (hbound : ∀ z ∈ phi.source, ∀ v : TangentSpace (𝓡 3) z,
      g.tangentNorm z v ≤ A * h.tangentNorm (phi z) (mfderiv (𝓡 3) (𝓡 3) phi z v)) :
    h.ball (phi x) (r / A) ⊆ phi '' g.ball x r := by
  let : EMetricSpace M := g.toEMetricSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hball : IsOpen (g.ball x r) := by
    change IsOpen {y : M | edist x y < ENNReal.ofReal r}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hx : x ∈ g.ball x r := by
    change edist x x < ENNReal.ofReal r
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hr
  have hxsource := hsource (subset_closure hx)
  let U := phi '' g.ball x r
  let K := phi '' closure (g.ball x r)
  have hU : IsOpen U := phi.toOpenPartialHomeomorph.isOpen_image_of_subset_source hball
    (fun _ hy => hsource (subset_closure hy))
  have hK : IsClosed K := (hcompact.image_of_continuousOn
    (phi.contMDiffOn_toFun.continuousOn.mono hsource)).isClosed
  have hUK : U ⊆ K := image_mono subset_closure
  have hKtarget : K ⊆ phi.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact phi.map_source (hsource hz)
  intro y hy
  by_contra hout
  obtain ⟨gamma, hzero, hone, hsmooth, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hy
  have hzeroU : gamma 0 ∈ U := hzero.symm ▸ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hpath, hexit⟩ := first_exit_compact hU hK hUK gamma hsmooth.continuousOn
    hzeroU (hone ▸ hout)
  have hsmall : Icc (0 : ℝ) s ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hs.2
  have hmaps : MapsTo gamma (Icc (0 : ℝ) s) phi.target := fun _ ht => hKtarget (hpath ht)
  have hlow : ENNReal.ofReal r ≤ g.edist (phi.invFun (gamma 0)) (phi.invFun (gamma s)) := by
    have hxleft : phi.invFun (phi x) = x := phi.left_inv hxsource
    rw [hzero, hxleft]
    apply le_of_not_gt
    intro hdist
    exact hexit ⟨phi.invFun (gamma s), hdist, phi.right_inv (hmaps ⟨hs.1.le, le_rfl⟩)⟩
  have hlift : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (phi.invFun ∘ gamma) (Icc 0 s) :=
    (phi.contMDiffOn_invFun.of_le (by simp)).comp (hsmooth.mono hsmall) hmaps
  have hd : g.edist (phi.invFun (gamma 0)) (phi.invFun (gamma s)) ≤
      g.pathELength (phi.invFun ∘ gamma) 0 s :=
    Manifold.riemannianEDist_le_pathELength hlift rfl rfl hs.1.le
  have hlen := pathELength_comp_le_of_tangentNorm_le h g phi.invFun phi.open_target
    phi.contMDiffOn_invFun hA.le (inverse_tangentNorm_bound g h phi A hbound)
      gamma 0 s (hsmooth.mono hsmall) hmaps
  have htotal : g.edist (phi.invFun (gamma 0)) (phi.invFun (gamma s)) ≤
      ENNReal.ofReal A * h.pathELength gamma 0 1 :=
    hd.trans (hlen.trans (mul_le_mul' le_rfl (Manifold.pathELength_mono le_rfl hs.2)))
  have hstrict : ENNReal.ofReal A * h.pathELength gamma 0 1 < ENNReal.ofReal r := by
    calc
      ENNReal.ofReal A * h.pathELength gamma 0 1 <
          ENNReal.ofReal A * ENNReal.ofReal (r / A) :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top hlength
      _ = ENNReal.ofReal (A * (r / A)) := (ENNReal.ofReal_mul hA.le).symm
      _ = ENNReal.ofReal r := congrArg ENNReal.ofReal (by field_simp [hA.ne'])
  exact (not_lt_of_ge hlow) (htotal.trans_lt hstrict)

end PoincareConjecture.M35
