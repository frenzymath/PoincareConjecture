import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaMotion
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BoundaryMotionTrace
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.EnergyIntegral
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.AttainmentRegularity










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators intervalIntegral

universe u

namespace PoincareConjecture.M65Filling

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem family_motion [T2Space M] [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) {J : Set ℝ} (hJ : IsOpen J)
    (C : M65SmoothFilledLoopFamily F J) (q : ℝ) (hq : q ∈ J)
    (hinj : Function.Injective (C.loops q : LoopCircle → M)) :
    ∃ (d : ℝ) (Phi : M × ℝ → M) (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p), 0 < d ∧
      (∀ s ∈ Ioo (-d) d, q + s ∈ J) ∧
      ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ Phi (univ ×ˢ Ioo (-d) d) ∧
      (∀ p, Phi (p, 0) = p) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun w : ℝ × M => (⟨w.2, V w.1 w.2⟩ : TangentBundle (𝓡 3) M)) ∧
      (∀ p s, s ∈ Ioo (-d) d →
        curveVelocity (n := 3) (fun r => Phi (p, r)) s = V (q + s) (Phi (p, s))) ∧
      ∀ s ∈ Ioo (-d) d, ∀ x : ℝ,
        Phi (periodicFreeLoop (C.loops q) x, s) = periodicFreeLoop (C.loops (q + s)) x := by
  have hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞
      (fun z : ℝ × ℝ => periodicFreeLoop (C.loops z.1) z.2) (J ×ˢ univ) :=
    C.joint_smooth.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn
      (fun _ hz => ⟨hz.2, hz.1⟩)
  obtain ⟨T, V, hT, hqT, hTJ, hV, hagree⟩ :=
    family_velocity_extension hJ C.loops hc q hq hinj (C.immersed q hq)
  obtain ⟨G, d, Phi, _hG, hMG, hd, htime, hPhi, hzero, hode⟩ :=
    compact_motion V T hT hV.contMDiffOn q hqT univ isCompact_univ
      ⟨periodicFreeLoop (C.loops q) 0, mem_univ _⟩
  have hGp (p : M) : p ∈ G := hMG (mem_univ p)
  let V' := fun s p => V (q + s) p
  have hV' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V' z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (univ ×ˢ univ) :=
    (hV.comp ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)).contMDiffOn
  have h0 : (0 : ℝ) ∈ Ioo (-d) d := by constructor <;> linarith
  refine ⟨d, Phi, V, hd, (fun s hs => hTJ (htime s hs)),
    hPhi.mono (fun z hz => ⟨hGp z.1, hz.2⟩), (fun p => hzero p (hGp p)), hV,
    (fun p s hs => (hode p (hGp p) s hs).2), ?_⟩
  intro s hs x
  have hsolutions := motion_eqOn V' univ isOpen_univ hV' (Ioo (-d) d)
    isOpen_Ioo isPreconnected_Ioo (subset_univ _) (fun r => Phi (periodicFreeLoop (C.loops q) x, r))
    (fun r => periodicFreeLoop (C.loops (q + r)) x) 0 h0
    (by simpa only [add_zero] using hzero (periodicFreeLoop (C.loops q) x) (hGp _))
    (fun r hr => hode _ (hGp _) r hr) (fun r hr => ?_)
  · exact hsolutions hs
  have htJ : q + r ∈ J := hTJ (htime r hr)
  have hbase : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3)
      (fun t => periodicFreeLoop (C.loops t) x) (q + r) :=
    ((hc.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨htJ, mem_univ x⟩)).comp
      (q + r) (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt).mdifferentiableAt (by simp)
  have hadd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => q + t) r :=
    (differentiableAt_const q |>.add differentiableAt_id).mdifferentiableAt
  refine ⟨hbase.comp r hadd, ?_⟩
  have hchain := mfderiv_comp r hbase hadd
  have hshift : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => q + t) r 1 = 1 := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv, id_eq] using!
      ((hasDerivAt_id r).const_add q).deriv
  have hh := congrArg (fun L : ℝ →L[ℝ]
      TangentSpace (𝓡 3) (periodicFreeLoop (C.loops (q + r)) x) => L 1) hchain
  change curveVelocity (n := 3) (fun t => periodicFreeLoop (C.loops (q + t)) x) r =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t => periodicFreeLoop (C.loops t) x) (q + r)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => q + t) r 1) at hh
  rw [hshift] at hh
  exact hh.trans (hagree (q + r) (htime r hr) x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem motion_tangent_smooth {T : Set ℝ} (hT : IsOpen T)
    (Phi : ℝ × M → M)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Phi (T ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) ((𝓡 3).prod (𝓡 3)) ∞
      (fun w : ℝ × TangentBundle (𝓡 3) M =>
        (⟨Phi (w.1, w.2.proj),
          mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) Phi (w.1, w.2.proj)
            (0, w.2.snd)⟩ : TangentBundle (𝓡 3) M)) (T ×ˢ univ) := by
  let P := (𝓘(ℝ, ℝ)).prod (𝓡 3)
  have hz : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ∞
      (fun w : ℝ × TangentBundle (𝓡 3) M =>
        (⟨w.1, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, ℝ)) (F := ℝ) (𝕜 := ℝ)
      (E := TangentSpace 𝓘(ℝ, ℝ))).comp contMDiff_fst
  have hlift : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      (P.prod 𝓘(ℝ, ℝ × LoopAmbient)) ∞
      (fun w : ℝ × TangentBundle (𝓡 3) M =>
        (⟨(w.1, w.2.proj), (0, w.2.snd)⟩ : TangentBundle P (ℝ × M))) :=
    contMDiff_equivTangentBundleProd_symm.comp (hz.prodMk contMDiff_snd)
  have htan := hPhi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    ((hT.prod isOpen_univ).uniqueMDiffOn)
  have h := htan.comp (hlift.contMDiffOn (s := T ×ˢ univ))
    (fun w (hw : w ∈ T ×ˢ univ) => ⟨hw.1, mem_univ _⟩)
  apply h.congr
  intro w hw
  change (⟨Phi (w.1, w.2.proj),
    mfderiv P (𝓡 3) Phi (w.1, w.2.proj) (0, w.2.snd)⟩ : TangentBundle (𝓡 3) M) =
      ⟨Phi (w.1, w.2.proj), mfderivWithin P (𝓡 3) Phi (T ×ˢ univ)
        (w.1, w.2.proj) (0, w.2.snd)⟩
  have he := mfderivWithin_of_isOpen (I := P) (I' := 𝓡 3) (f := Phi)
    (x := (w.1, w.2.proj)) (hT.prod isOpen_univ) ⟨hw.1, mem_univ _⟩
  exact congrArg (fun L : TangentSpace P (w.1, w.2.proj) →L[ℝ]
      TangentSpace (𝓡 3) (Phi (w.1, w.2.proj)) =>
    (⟨Phi (w.1, w.2.proj), L (0, w.2.snd)⟩ : TangentBundle (𝓡 3) M)) he.symm

private noncomputable def motionEnergy {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (Phi : ℝ × M → M) (w : ℝ × TangentBundle (𝓡 3) M) : ℝ :=
  (1 / 2 : ℝ) * (F.metric w.1).inner (Phi (w.1, w.2.proj))
    (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) Phi (w.1, w.2.proj) (0, w.2.snd))
    (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) Phi (w.1, w.2.proj) (0, w.2.snd))

set_option backward.isDefEq.respectTransparency false in
private theorem motionEnergy_smooth {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    {T : Set ℝ} (hT : IsOpen T) (hTF : T ⊆ Ioo a b) (Phi : ℝ × M → M)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Phi (T ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) 𝓘(ℝ, ℝ) ∞
      (motionEnergy F Phi) (T ×ˢ univ) := by
  intro w hw
  have hcol := (motion_tangent_smooth hT Phi hPhi).contMDiffAt
    ((hT.prod isOpen_univ).mem_nhds hw)
  have hbase := (Bundle.contMDiffAt_proj (TangentSpace (𝓡 3))).comp w hcol
  have hm := (F.smooth.contMDiffAt
    (prod_mem_nhds (Icc_mem_nhds (hTF hw.1).1 (hTF hw.1).2) univ_mem)).comp w
      (contMDiffAt_fst.prodMk hbase)
  have hp := hm.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hcol hcol
  have hh := (Bundle.contMDiffAt_totalSpace.mp hp).2
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply] at hh
  exact (contMDiffAt_const.mul hh).contMDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_timePartial_continuousOn {T : Set ℝ} (hT : IsOpen T)
    (H : ℝ × TangentBundle (𝓡 3) M → ℝ)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) 𝓘(ℝ, ℝ) 1 H (T ×ˢ univ)) :
    ContinuousOn (fun w : ℝ × TangentBundle (𝓡 3) M => deriv (fun t => H (t, w.2)) w.1)
      (T ×ˢ univ) := by
  intro w hw
  have hp : ContMDiffAt
      (((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 1
      (Function.uncurry (fun p : ℝ × TangentBundle (𝓡 3) M => fun t => H (t, p.2)))
      (w, w.1) :=
    (hH.contMDiffAt ((hT.prod isOpen_univ).mem_nhds hw)).comp (w, w.1)
      (contMDiffAt_snd.prodMk contMDiffAt_fst.snd)
  have hd := hp.mfderiv (fun p : ℝ × TangentBundle (𝓡 3) M => fun t => H (t, p.2))
    Prod.fst (m := 0) contMDiffAt_fst (by norm_num)
  have hh := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
  have hresult : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) 𝓘(ℝ, ℝ) 0
      (fun p : ℝ × TangentBundle (𝓡 3) M => deriv (fun t => H (t, p.2)) p.1) w := by
    simpa +instances only [inTangentCoordinates_model_space, mfderiv_eq_fderiv,
      fderiv_apply_one_eq_deriv] using! hh
  exact hresult.continuousAt.continuousWithinAt

private noncomputable def diskColumn (f : LoopPlane → M) (i : Fin 2)
    (z : LoopPlane) : TangentBundle (𝓡 3) M :=
  ⟨f z, mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩

private noncomputable def diskEnergyTrace {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (Phi : ℝ × M → M) (f : LoopPlane → M) (w : ℝ × LoopPlane) : ℝ :=
  ∑ i : Fin 2, motionEnergy F Phi (w.1, diskColumn f i w.2)

private noncomputable def diskEnergyDerivativeTrace {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (Phi : ℝ × M → M) (f : LoopPlane → M) (w : ℝ × LoopPlane) : ℝ :=
  ∑ i : Fin 2, deriv (fun t => motionEnergy F Phi (t, diskColumn f i w.2)) w.1

set_option backward.isDefEq.respectTransparency false in
private theorem diskEnergyTrace_eq {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    {T : Set ℝ} (hT : IsOpen T) (Phi : ℝ × M → M)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Phi (T ×ˢ univ))
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    {t : ℝ} (ht : t ∈ T) {z : LoopPlane} (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
    diskEnergyTrace F Phi f (t, z) =
      m60EnergyDensity (F.metric t) (fun y => Phi (t, f y)) z := by
  have hn : loopDiskSet ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hd := (hf.contMDiffAt hn).mdifferentiableAt one_ne_zero
  have hP := (hPhi.contMDiffAt (x := (t, f z)) ((hT.prod isOpen_univ).mem_nhds
    ⟨ht, mem_univ (f z)⟩)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z hP (mdifferentiableAt_const.prodMk hd)
  have hcol (i : Fin 2) : mfderiv (𝓡 2) (𝓡 3) (fun y => Phi (t, f y)) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) Phi (t, f z)
        (0, (diskColumn f i z).snd) := by
    rw [mfderiv_prodMk mdifferentiableAt_const hd, mfderiv_const] at hchain
    have hh := congrArg (fun L : LoopPlane →L[ℝ] TangentSpace (𝓡 3) (Phi (t, f z)) =>
      L (EuclideanSpace.basisFun (Fin 2) ℝ i)) hchain
    simpa +instances only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply, diskColumn,
      mfderivWithin_of_mem_nhds hn] using! hh
  simp only [diskEnergyTrace, motionEnergy, diskColumn, m60EnergyDensity,
    Matrix.trace, Matrix.diag_apply, m60AreaGram, hcol, Finset.mul_sum]

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
private theorem diskEnergyTrace_continuous {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    {T : Set ℝ} (hT : IsOpen T) (hTF : T ⊆ Ioo a b) (Phi : ℝ × M → M)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Phi (T ×ˢ univ))
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet) :
    ContinuousOn (diskEnergyTrace F Phi f) (T ×ˢ loopDiskSet) ∧
      ContinuousOn (diskEnergyDerivativeTrace F Phi f) (T ×ˢ loopDiskSet) := by
  have hK := motionEnergy_smooth F hT hTF Phi hPhi
  have hKt := scalar_timePartial_continuousOn hT (motionEnergy F Phi)
    (hK.of_le (by simp))
  have harg (i : Fin 2) : ContinuousOn
      (fun w : ℝ × LoopPlane => (w.1, diskColumn f i w.2)) (T ×ˢ loopDiskSet) :=
    continuousOn_fst.prodMk
      ((m65Attainment_continuousWithin_column hf (EuclideanSpace.basisFun (Fin 2) ℝ i)).comp
        continuousOn_snd (fun _ hw => hw.2))
  have hE (i : Fin 2) : ContinuousOn
      (fun w : ℝ × LoopPlane => motionEnergy F Phi (w.1, diskColumn f i w.2))
      (T ×ˢ loopDiskSet) :=
    hK.continuousOn.comp (harg i) (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hD (i : Fin 2) : ContinuousOn
      (fun w : ℝ × LoopPlane => deriv (fun t => motionEnergy F Phi (t, diskColumn f i w.2)) w.1)
      (T ×ˢ loopDiskSet) := by
    convert! hKt.comp (harg i) (fun _ hw => ⟨hw.1, mem_univ _⟩) using 1
  constructor
  · apply ((hE 0).add (hE 1)).congr
    intro w _
    simp only [diskEnergyTrace, Fin.sum_univ_two, Pi.add_apply]
  · apply ((hD 0).add (hD 1)).congr
    intro w _
    simp only [diskEnergyDerivativeTrace, Fin.sum_univ_two, Pi.add_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem diskEnergyTrace_hasDerivAt {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    {T : Set ℝ} (hT : IsOpen T) (hTF : T ⊆ Ioo a b) (Phi : ℝ × M → M)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Phi (T ×ˢ univ))
    (f : LoopPlane → M) {t : ℝ} (ht : t ∈ T) (z : LoopPlane) :
    HasDerivAt (fun r => diskEnergyTrace F Phi f (r, z))
      (diskEnergyDerivativeTrace F Phi f (t, z)) t := by
  have hK := motionEnergy_smooth F hT hTF Phi hPhi
  apply HasDerivAt.fun_sum
  intro i _
  have hs := (hK.contMDiffAt (x := (t, diskColumn f i z)) ((hT.prod isOpen_univ).mem_nhds
    ⟨ht, mem_univ (diskColumn f i z)⟩)).comp t
      (contMDiffAt_id.prodMk (contMDiffAt_const (c := diskColumn f i z)))
  exact (hs.contDiffAt.differentiableAt (by simp)).hasDerivAt

private theorem diskEnergy_integral_hasDerivAt {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    {T : Set ℝ} (hT : IsOpen T) (hTF : T ⊆ Ioo a b) (Phi : ℝ × M → M)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Phi (T ×ˢ univ))
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    {t : ℝ} (ht : t ∈ T) :
    IntegrableOn (fun z => diskEnergyDerivativeTrace F Phi f (t, z)) loopDiskSet volume ∧
      HasDerivAt (fun r => ∫ z in loopDiskSet,
        m60EnergyDensity (F.metric r) (fun y => Phi (r, f y)) z)
        (∫ z in loopDiskSet, diskEnergyDerivativeTrace F Phi f (t, z)) t := by
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds ht)
  have hsmall : Metric.closedBall t (δ / 2) ⊆ T := by
    intro r hr
    exact hδT (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hr) (by linarith)))
  obtain ⟨hE, hD⟩ := diskEnergyTrace_continuous F hT hTF Phi hPhi f hf
  obtain ⟨hI, hder⟩ := m65HasDerivAt_integral_loopDisk_of_trace
    (diskEnergyTrace F Phi f) (diskEnergyDerivativeTrace F Phi f) (by positivity : 0 < δ / 2)
    (hE.mono (prod_mono hsmall Subset.rfl)) (hD.mono (prod_mono hsmall Subset.rfl))
    (fun z _ r hr => diskEnergyTrace_hasDerivAt F hT hTF Phi hPhi f (hsmall hr) z)
  refine ⟨hI, hder.congr_of_eventuallyEq ?_⟩
  filter_upwards [hT.mem_nhds ht] with r hr
  apply integral_congr_ae
  filter_upwards [m65Ae_mem_openLoopDisk] with z hz
  exact (diskEnergyTrace_eq F hT Phi hPhi f hf hr hz).symm

set_option backward.isDefEq.respectTransparency false in
private theorem ambientColumnTrace_continuous {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p => (⟨p, W p⟩ : TangentBundle (𝓡 3) M)))
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet) (i : Fin 2) :
    ContinuousOn (fun z => (⟨f z,
      D.connection W (f z) (diskColumn f i z).snd⟩ : TangentBundle (𝓡 3) M)) loopDiskSet := by
  have hconn := D.smooth.contMDiff.contMDiff (σ := W) (by simpa using hW.contMDiffOn)
  have hc := hconn.continuousOn.comp hf.continuousOn (fun _ _ => mem_univ _)
  exact hc.clm_bundle_apply
    (m65Attainment_continuousWithin_column hf (EuclideanSpace.basisFun (Fin 2) ℝ i))

set_option backward.isDefEq.respectTransparency false in
private theorem ambientColumn_eq {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (u : ℝ → LoopPlane → M) {U : Set (ℝ × LoopPlane)}
    (hU : IsOpen U)
    (hu : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (Function.uncurry u) U)
    {t : ℝ} {z : LoopPlane} (htz : (t, z) ∈ U)
    (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p => (⟨p, W p⟩ : TangentBundle (𝓡 3) M)))
    (hvel : ∀ y, curveVelocity (n := 3) (fun r => u r y) t = W (u t y)) (v : LoopPlane) :
    rampHorizontalCovariantDerivative D (fun r => u r z)
      (fun r => mfderiv (𝓡 2) (𝓡 3) (u r) z v) t =
        D.connection W (u t z) (mfderiv (𝓡 2) (𝓡 3) (u t) z v) := by
  have hslice : MDifferentiableAt (𝓡 2) (𝓡 3) (u t) z :=
    ((hu.contMDiffAt (hU.mem_nhds htz)).comp z
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hline : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) (fun r : ℝ => z + r • v) 0 :=
    (contDiffAt_const (n := ∞) |>.add (contDiffAt_id.smul contDiffAt_const)).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => u t (z + r • v)) 0 := by
    have hh : MDifferentiableAt (𝓡 2) (𝓡 3) (u t) (z + (0 : ℝ) • v) := by
      simpa only [zero_smul, add_zero] using hslice
    exact hh.comp 0 hline
  rw [m65PlaneCovariantColumn_commute D u hU hu htz v]
  have heq := M62.pullback_congr D (γ := fun r : ℝ => u t (z + r • v)) (x := 0)
    (Filter.Eventually.of_forall (fun r => hvel (z + r • v)))
  rw [heq, M62.pullback_ambient_field D hcurve W (hW.mdifferentiableAt (by simp))]
  have hpoint : z + (0 : ℝ) • v = z := by simp
  rw [hpoint, m65CurveVelocity_affineLine hslice v]

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in




theorem disk_energy_firstVariation {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    {T : Set ℝ} (hT : IsOpen T) (hTF : T ⊆ Ioo a b) (Phi : ℝ × M → M)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Phi (T ×ˢ univ))
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hfi : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (Metric.ball (0 : LoopPlane) 1))
    {t : ℝ} (ht : t ∈ T) (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p => (⟨p, W p⟩ : TangentBundle (𝓡 3) M)))
    (hvel : ∀ p, curveVelocity (n := 3) (fun r => Phi (r, p)) t = W (Phi (t, p)))
    (hconf : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram (F.metric t) (fun y => Phi (t, f y)) z =
        c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (htension : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      m65PlaneTension (F.connection t) (fun y => Phi (t, f y)) z = 0) :
    IntegrableOn (m65PlaneRicciTraceDensity (F.connection t) (fun y => Phi (t, f y)))
        loopDiskSet volume ∧
      HasDerivAt (fun r => ∫ z in loopDiskSet,
        m60EnergyDensity (F.metric r) (fun y => Phi (r, f y)) z)
        (-(∫ z in loopDiskSet,
          m65PlaneRicciTraceDensity (F.connection t) (fun y => Phi (t, f y)) z) +
          ∫ θ in (-Real.pi)..Real.pi,
            (F.metric t).inner (Phi (t, f (Proofs.M58.angularPoint θ)))
              (W (Phi (t, f (Proofs.M58.angularPoint θ))))
              (mfderivWithin (𝓡 2) (𝓡 3) (fun y => Phi (t, f y)) loopDiskSet
                (Proofs.M58.angularPoint θ) (Proofs.M58.angularPoint θ))) t := by
  let u := fun r z => Phi (r, f z)
  let U := T ×ˢ Metric.ball (0 : LoopPlane) 1
  have hU : IsOpen U := hT.prod Metric.isOpen_ball
  have hu : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (Function.uncurry u) U :=
    hPhi.comp (contMDiff_fst.contMDiffOn.prodMk
      (hfi.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2)))
      (fun _ hz => ⟨hz.1, mem_univ _⟩)
  have hPt : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Phi (t, p)) univ :=
    hPhi.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun _ _ => ⟨ht, mem_univ _⟩)
  have huf : ContMDiffOn (𝓡 2) (𝓡 3) 1 (u t) loopDiskSet :=
    (hPt.of_le (by simp)).comp hf (fun _ _ => mem_univ _)
  let E := fun z i => (diskColumn (u t) i z).snd
  let A := fun z i => (F.connection t).connection W (u t z) (E z i)
  have hV : ContinuousOn (fun z => (⟨u t z, W (u t z)⟩ : TangentBundle (𝓡 3) M))
      loopDiskSet := hW.continuous.comp_continuousOn huf.continuousOn
  have hE (i : Fin 2) : ContinuousOn
      (fun z => (⟨u t z, E z i⟩ : TangentBundle (𝓡 3) M)) loopDiskSet :=
    m65Attainment_continuousWithin_column huf (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hA (i : Fin 2) : ContinuousOn
      (fun z => (⟨u t z, A z i⟩ : TangentBundle (𝓡 3) M)) loopDiskSet :=
    ambientColumnTrace_continuous (F.connection t) W hW (u t) huf i
  have hEe (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) (i : Fin 2) :
      E z i = mfderiv (𝓡 2) (𝓡 3) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    have hn : loopDiskSet ∈ 𝓝 z :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
    dsimp only [E, diskColumn]
    rw [mfderivWithin_of_mem_nhds hn]
  have hAe (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) (i : Fin 2) :
      A z i = rampHorizontalCovariantDerivative (F.connection t) (fun r => u r z)
        (fun r => mfderiv (𝓡 2) (𝓡 3) (u r) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) t := by
    have hh := ambientColumn_eq (F.connection t) u hU hu ⟨ht, hz⟩ W hW
      (fun y => hvel (f y)) (EuclideanSpace.basisFun (Fin 2) ℝ i)
    simpa only [A, hEe z hz i] using hh.symm
  obtain ⟨hAI, hflux⟩ := m65Integral_motionDensity_eq_boundary_of_trace F u hU hu
    (fun z hz => ⟨ht, hz⟩) (fun z => W (u t z)) E A hV hE hA
    (fun z _ => (hvel (f z)).symm) hEe hAe hconf htension
  obtain ⟨hI, hder⟩ := diskEnergy_integral_hasDerivAt F hT hTF Phi hPhi f hf ht
  let R := m65PlaneRicciTraceDensity (F.connection t) (u t)
  let B := m65PlaneMotionDensity F u t
  have hBI : IntegrableOn B loopDiskSet volume := hAI
  have hjet : (fun z => diskEnergyDerivativeTrace F Phi f (t, z))
      =ᵐ[volume.restrict loopDiskSet] (fun z => -R z + B z) := by
    filter_upwards [m65Ae_mem_openLoopDisk] with z hz
    obtain ⟨c, hc⟩ := hconf z hz
    have htwo : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) 2
        (Function.uncurry u) (t, z) :=
      ((hu (t, z) ⟨ht, hz⟩).contMDiffAt (hU.mem_nhds ⟨ht, hz⟩)).of_le (by decide)
    have hp : HasDerivAt (fun r => m60EnergyDensity (F.metric r) (u r) z)
        (diskEnergyDerivativeTrace F Phi f (t, z)) t := by
      apply (diskEnergyTrace_hasDerivAt F hT hTF Phi hPhi f ht z).congr_of_eventuallyEq
      filter_upwards [hT.mem_nhds ht] with r hr
      exact (diskEnergyTrace_eq F hT Phi hPhi f hf hr hz).symm
    exact hp.unique (m65MovingEnergyDensity_hasDerivAt_of_conformal F u (hTF ht) htwo c hc)
  have hRI : IntegrableOn R loopDiskSet volume := by
    apply (hAI.sub hI).congr
    filter_upwards [hjet] with z hz
    change B z - diskEnergyDerivativeTrace F Phi f (t, z) = R z
    rw [hz]
    ring
  refine ⟨hRI, hder.congr_deriv ?_⟩
  calc
    _ = ∫ z in loopDiskSet, -R z + B z := integral_congr_ae hjet
    _ = (∫ z in loopDiskSet, -R z) + ∫ z in loopDiskSet, B z := integral_add hRI.neg hBI
    _ = -(∫ z in loopDiskSet, R z) + ∫ z in loopDiskSet, B z := by rw [integral_neg]
    _ = _ := by
      rw [hflux]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      let D := mfderivWithin (𝓡 2) (𝓡 3) (u t) loopDiskSet (Proofs.M58.angularPoint θ)
      have hrad : (∑ i : Fin 2, (Proofs.M58.angularPoint θ) i •
          D (EuclideanSpace.basisFun (Fin 2) ℝ i)) = D (Proofs.M58.angularPoint θ) := by
        simp_rw [← map_smul]
        rw [← map_sum]
        congr 1
        exact (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr (Proofs.M58.angularPoint θ)
      exact congrArg ((F.metric t).inner (u t (Proofs.M58.angularPoint θ))
        (W (u t (Proofs.M58.angularPoint θ)))) hrad

end PoincareConjecture.M65Filling
