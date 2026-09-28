import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMotionEnergy





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {k : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin k)) N] [IsManifold (𝓡 k) ∞ N]
  {a b : ℝ}




def m64AnnulusMotionEnergyTrace (F : RicciFlow k N (Icc a b))
    (time : ℝ) (Phi : ℝ × M → N) (r : ℝ) (f : LoopPlane → M)
    (w : ℝ × LoopPlane) : ℝ :=
  r * m64AmbientMotionEnergy (n := n) F time Phi (w.1, m64AnnulusWithinColumn f 0 w.2) +
    r⁻¹ * m64AmbientMotionEnergy (n := n) F time Phi (w.1, m64AnnulusWithinColumn f 1 w.2)




def m64AnnulusMotionEnergyDerivativeTrace (F : RicciFlow k N (Icc a b))
    (time : ℝ) (Phi : ℝ × M → N) (r : ℝ) (f : LoopPlane → M)
    (w : ℝ × LoopPlane) : ℝ :=
  r * deriv (fun s => m64AmbientMotionEnergy (n := n) F time Phi
    (s, m64AnnulusWithinColumn f 0 w.2)) w.1 +
    r⁻¹ * deriv (fun s => m64AmbientMotionEnergy (n := n) F time Phi
      (s, m64AnnulusWithinColumn f 1 w.2)) w.1

omit [IsManifold (𝓡 n) ∞ M] in




theorem m64AnnulusMotionEnergyTrace_eq (F : RicciFlow k N (Icc a b))
    (time : ℝ) {T : Set ℝ} (hT : IsOpen T) {O : Set M} (hO : IsOpen O)
    (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi (T ×ˢ O))
    (r : ℝ) {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (hfO : MapsTo f m64AnnulusDomain O)
    {s : ℝ} (hs : s ∈ T) {p : LoopPlane} (hp : p ∈ interior m64AnnulusDomain) :
    m64AnnulusMotionEnergyTrace (n := n) F time Phi r f (s, p) =
      m64ModulusEnergyDensity (F.metric (time + s)) r (fun y => Phi (s, f y)) p := by
  have hn : m64AnnulusDomain ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hp
  have hd := (hf.contMDiffAt hn).mdifferentiableAt one_ne_zero
  have hP := (hPhi.contMDiffAt (x := (s, f p)) ((hT.prod hO).mem_nhds
    ⟨hs, hfO (interior_subset hp)⟩)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp p hP (mdifferentiableAt_const.prodMk hd)
  have hcol (i : Fin 2) : mfderiv (𝓡 2) (𝓡 k) (fun y => Phi (s, f y)) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) Phi (s, f p)
        (0, (m64AnnulusWithinColumn (n := n) f i p).snd) := by
    rw [mfderiv_prodMk mdifferentiableAt_const hd, mfderiv_const] at hchain
    have hh := congrArg (fun L : LoopPlane →L[ℝ] TangentSpace (𝓡 k) (Phi (s, f p)) =>
      L (EuclideanSpace.basisFun (Fin 2) ℝ i)) hchain
    simpa +instances only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply, m64AnnulusWithinColumn,
      mfderivWithin_of_mem_nhds hn] using! hh
  simp only [m64AnnulusMotionEnergyTrace, m64AmbientMotionEnergy,
    m64AmbientMotionTangent, m64AnnulusWithinColumn, m64ModulusEnergyDensity,
    m60AreaGram, hcol]
  ring





theorem m64AnnulusMotionEnergyTrace_continuous (F : RicciFlow k N (Icc a b))
    (time : ℝ) {T : Set ℝ} (hT : IsOpen T) {O : Set M} (hO : IsOpen O)
    (hTF : ∀ s ∈ T, time + s ∈ Ioo a b) (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi (T ×ˢ O))
    (r : ℝ) {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (hfO : MapsTo f m64AnnulusDomain O) :
    ContinuousOn (m64AnnulusMotionEnergyTrace (n := n) F time Phi r f)
        (T ×ˢ m64AnnulusDomain) ∧
      ContinuousOn (m64AnnulusMotionEnergyDerivativeTrace (n := n) F time Phi r f)
        (T ×ˢ m64AnnulusDomain) := by
  have hK := m64AmbientMotionEnergy_contMDiffOn F time hT hO hTF Phi hPhi
  have hV : IsOpen {v : TangentBundle (𝓡 n) M | v.proj ∈ O} :=
    hO.preimage (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)))
  have hKt := m64TangentScalar_timePartial_continuousOn hT hV
    (m64AmbientMotionEnergy F time Phi) (hK.of_le (by simp))
  have harg (i : Fin 2) : ContinuousOn
      (fun w : ℝ × LoopPlane => (w.1, m64AnnulusWithinColumn (n := n) f i w.2))
      (T ×ˢ m64AnnulusDomain) :=
    continuousOn_fst.prodMk ((m64AnnulusWithinColumn_continuousOn hf i).comp
      continuousOn_snd (fun _ hw => hw.2))
  have hE (i : Fin 2) : ContinuousOn
      (fun w : ℝ × LoopPlane => m64AmbientMotionEnergy (n := n) F time Phi
        (w.1, m64AnnulusWithinColumn f i w.2)) (T ×ˢ m64AnnulusDomain) :=
    hK.continuousOn.comp (harg i) (fun _ hw => ⟨hw.1, hfO hw.2⟩)
  have hD (i : Fin 2) : ContinuousOn
      (fun w : ℝ × LoopPlane => deriv (fun s => m64AmbientMotionEnergy (n := n) F time Phi
        (s, m64AnnulusWithinColumn f i w.2)) w.1) (T ×ˢ m64AnnulusDomain) := by
    convert! hKt.comp (harg i) (fun _ hw => ⟨hw.1, hfO hw.2⟩) using 1
  exact ⟨((hE 0).const_mul r).add ((hE 1).const_mul r⁻¹),
    ((hD 0).const_mul r).add ((hD 1).const_mul r⁻¹)⟩





theorem m64AnnulusMotionEnergyTrace_hasDerivAt (F : RicciFlow k N (Icc a b))
    (time : ℝ) {T : Set ℝ} (hT : IsOpen T) {O : Set M} (hO : IsOpen O)
    (hTF : ∀ s ∈ T, time + s ∈ Ioo a b) (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi (T ×ˢ O))
    (r : ℝ) (f : LoopPlane → M) {s : ℝ} (hs : s ∈ T)
    (p : LoopPlane) (hp : f p ∈ O) :
    HasDerivAt (fun z => m64AnnulusMotionEnergyTrace (n := n) F time Phi r f (z, p))
      (m64AnnulusMotionEnergyDerivativeTrace (n := n) F time Phi r f (s, p)) s := by
  have hK := m64AmbientMotionEnergy_contMDiffOn F time hT hO hTF Phi hPhi
  have hV : IsOpen {v : TangentBundle (𝓡 n) M | v.proj ∈ O} :=
    hO.preimage (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)))
  have hi (i : Fin 2) : HasDerivAt
      (fun z => m64AmbientMotionEnergy (n := n) F time Phi (z, m64AnnulusWithinColumn f i p))
      (deriv (fun z => m64AmbientMotionEnergy (n := n) F time Phi
        (z, m64AnnulusWithinColumn f i p)) s) s := by
    have h := (hK.contMDiffAt (x := (s, m64AnnulusWithinColumn f i p))
      ((hT.prod hV).mem_nhds ⟨hs, hp⟩)).comp s
        (contMDiffAt_id.prodMk (contMDiffAt_const (c := m64AnnulusWithinColumn f i p)))
    exact (h.contDiffAt.differentiableAt (by simp)).hasDerivAt
  exact ((hi 0).const_mul r).add ((hi 1).const_mul r⁻¹)

end PoincareConjecture
