import PoincareConjecture.Proofs.M09.InteriorPointVariation
import PoincareConjecture.Proofs.M09.JoinStationarity
import PoincareConjecture.Proofs.M09.PrefixMinimality
import PoincareConjecture.Proofs.M09.UniqueMinimizingVectors
import PoincareConjecture.Proofs.M09.FamilyPhaseIdentification
import PoincareConjecture.Proofs.M09.InverseChartVector








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_uniqueMinimizing_prefix
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b (hc.trans hcb) hmax)) :
    A.uniqueMinimizing Z c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hb : 0 < b := hc.trans hcb
  have hcmax : c < τmax := hcb.trans hmax
  have hprefix := lExponentialFamily_minimizing_prefix hM04 hτmax hwindow hL
    A Z c b hc hcb hmax hmin
  apply (lExponentialFamily_uniqueMinimizing_iff hM04 hL hτmax hwindow A Z c hc hcmax).mpr
  refine ⟨hprefix, ?_⟩
  intro W hend hWmin
  have hstart : (A.path W c hc hcmax).curve 0 = (A.path Z c hc hcmax).curve 0 := by
    simp only [A.path_eq, A.gamma_at_zero]
  have hend' : (A.path W c hc hcmax).curve c = (A.path Z c hc hcmax).curve c := by
    simpa only [A.path_eq] using hend
  have haction : A.action W c = A.action Z c := by
    apply le_antisymm
    · simpa only [LExponentialFamily.action, A.path_eq] using
        hWmin (A.path Z c hc hcmax) hstart.symm hend'.symm
    · simpa only [LExponentialFamily.action, A.path_eq] using
        hprefix (A.path W c hc hcmax) hstart hend'
  have hsc : Real.sqrt c ∈ Set.Ico 0 (Real.sqrt τmax) :=
    ⟨Real.sqrt_nonneg c, Real.sqrt_lt_sqrt hc.le hcmax⟩
  have hsb : Real.sqrt b ∈ Set.Ico 0 (Real.sqrt τmax) :=
    ⟨Real.sqrt_nonneg b, Real.sqrt_lt_sqrt hb.le hmax⟩
  have hpoint : A.squareFamily W (Real.sqrt c) = A.squareFamily Z (Real.sqrt c) := by
    rw [A.square_agrees W _ hsc, A.square_agrees Z _ hsc, Real.sq_sqrt hc.le]
    exact hend
  let q := A.squareFamily Z (Real.sqrt c)
  let e := chartAt Q q
  let y0 := e q
  let D : TangentSpace (𝓡 n) p → Set ℝ :=
    fun Y ↦ (fun s : ℝ ↦ (Y, s)) ⁻¹' A.squareDomain
  have hD (Y : TangentSpace (𝓡 n) p) : IsOpen (D Y) :=
    A.square_open.preimage (continuous_const.prodMk continuous_id)
  have hDI (Y : TangentSpace (𝓡 n) p) : Set.Icc 0 (Real.sqrt b) ⊆ D Y := by
    intro s hs
    exact A.square_contains ⟨Set.mem_univ _, hs.1, hs.2.trans_lt hsb.2⟩
  have hAsmooth : ContMDiffOn (𝓘(ℝ, TangentSpace (𝓡 n) p × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.squareFamily z.1 z.2) A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hslice (Y : TangentSpace (𝓡 n) p) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Y) (D Y) :=
    hAsmooth.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      (fun _ hs ↦ hs)
  have hmarkTime : Real.sqrt c ∈ Set.Ioo 0 (Real.sqrt b) :=
    ⟨Real.sqrt_pos.mpr hc, Real.sqrt_lt_sqrt hc.le hcb⟩
  have hpair (v : Q) :
      (F.metric (T - c)).inner q (curveVelocity (n := n) (A.squareFamily W) (Real.sqrt c))
          (mfderiv (𝓡 n) (𝓡 n) e.symm y0 v) =
        (F.metric (T - c)).inner q (curveVelocity (n := n) (A.squareFamily Z) (Real.sqrt c))
          (mfderiv (𝓡 n) (𝓡 n) e.symm y0 v) := by
    obtain ⟨f, Uf, ρf, hUf, hρf, hIf, hf, hfcenter, hfleft, _, hfmark, hfv⟩ :=
      exists_smooth_interior_point_variation (A.squareFamily W) (D W) (hD W) (hslice W)
        (Real.sqrt b) (Real.sqrt c) hmarkTime (hDI W) v
    obtain ⟨g, Ug, ρg, hUg, hρg, hIg, hg, hgcenter, hgleft, hgright, hgmark, hgv⟩ :=
      exists_smooth_interior_point_variation (A.squareFamily Z) (D Z) (hD Z) (hslice Z)
        (Real.sqrt b) (Real.sqrt c) hmarkTime (hDI Z) v
    let ρ := min ρf ρg
    have hρ : 0 < ρ := lt_min hρf hρg
    have hfparam : Set.Ioo (-ρ) ρ ⊆ Set.Ioo (-ρf) ρf := by
      intro u hu
      exact ⟨(neg_le_neg (min_le_left ρf ρg)).trans_lt hu.1,
        hu.2.trans_le (min_le_left ρf ρg)⟩
    have hgparam : Set.Ioo (-ρ) ρ ⊆ Set.Ioo (-ρg) ρg := by
      intro u hu
      exact ⟨(neg_le_neg (min_le_right ρf ρg)).trans_lt hu.1,
        hu.2.trans_le (min_le_right ρf ρg)⟩
    have hI : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ Uf ∩ Ug :=
      fun z hz ↦ ⟨hIf ⟨hz.1, hfparam hz.2⟩, hIg ⟨hz.1, hgparam hz.2⟩⟩
    have hp := lExponentialFamily_join_momentum_pairing hM04 hL hτmax hwindow A Z W
      c b hc hcb hmax hmin haction f g (Uf ∩ Ug) (hUf.inter hUg)
      (hf.mono Set.inter_subset_left) (hg.mono Set.inter_subset_right) ρ hρ hI
      hfcenter hgcenter (fun u _ ↦ (hfleft u).trans (A.square_at_zero W))
      (fun u _ ↦ (hgleft u).trans (A.square_at_zero Z))
      (fun u _ ↦ (hgright u).trans (by rw [A.square_agrees Z _ hsb, Real.sq_sqrt hb.le]))
      (fun u _ ↦ by rw [hfmark, hgmark, hpoint])
    rw [hfv, hgv, hpoint] at hp
    exact hp
  let vW : Q := curveVelocity (n := n) (A.squareFamily W) (Real.sqrt c)
  let vZ : Q := curveVelocity (n := n) (A.squareFamily Z) (Real.sqrt c)
  have hv : vW = vZ := by
    obtain ⟨v, hv⟩ := (inverseChartDifferential_bijective q y0
      (e.map_source (mem_chart_source Q q))).surjective (vW - vZ)
    have hp := hpair v
    rw [hv] at hp
    have hzero : (F.metric (T - c)).inner q (vW - vZ) (vW - vZ) = 0 := by
      have hsub := congrArg (fun L : TangentSpace (𝓡 n) q →L[ℝ] ℝ ↦ L (vW - vZ))
        (((F.metric (T - c)).inner q).map_sub (vW : TangentSpace (𝓡 n) q) vZ)
      exact hsub.trans (sub_eq_zero.mpr hp)
    by_contra hne
    exact (ne_of_gt ((F.metric (T - c)).pos q (vW - vZ) (sub_ne_zero.mpr hne))) hzero
  apply lExponentialFamily_initialVector_eq_of_squarePhase hM04 hτmax hwindow A W Z b hb hmax
    (Real.sqrt c) ⟨Real.sqrt_nonneg c, (Real.sqrt_le_sqrt hcb.le)⟩
  exact Bundle.TotalSpace.ext hpoint (heq_of_eq hv)

end PoincareConjecture.Proofs.M09
