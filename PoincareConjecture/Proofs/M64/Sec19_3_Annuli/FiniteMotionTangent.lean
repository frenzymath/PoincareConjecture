import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ClosedRectangleEnergyVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMovingMetricDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def m64AnnulusWithinColumn (f : LoopPlane → M) (i : Fin 2)
    (p : LoopPlane) : TangentBundle (𝓡 n) M :=
  ⟨f p, mfderivWithin (𝓡 2) (𝓡 n) f m64AnnulusDomain p
    (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩

theorem m64AnnulusWithinColumn_continuousOn {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain) (i : Fin 2) :
    ContinuousOn (m64AnnulusWithinColumn (n := n) f i) m64AnnulusDomain :=
  (hf.continuousOn_tangentMapWithin le_rfl m64AnnulusDomain_uniqueDiffOn.uniqueMDiffOn).comp
    (((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn) (fun _ hp => hp)

variable {k : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin k)) N] [IsManifold (𝓡 k) ∞ N]

def m64AmbientMotionTangent (Phi : ℝ × M → N)
    (w : ℝ × TangentBundle (𝓡 n) M) : TangentBundle (𝓡 k) N :=
  ⟨Phi (w.1, w.2.proj),
    mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) Phi (w.1, w.2.proj) (0, w.2.snd)⟩

theorem m64AmbientMotionTangent_contMDiffOn {T : Set ℝ} (hT : IsOpen T)
    {O : Set M} (hO : IsOpen O) (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi (T ×ˢ O)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) ((𝓡 k).prod (𝓡 k)) ∞
      (m64AmbientMotionTangent (n := n) (k := k) Phi)
      (T ×ˢ {v : TangentBundle (𝓡 n) M | v.proj ∈ O}) := by
  let P := (𝓘(ℝ, ℝ)).prod (𝓡 n)
  have hz : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n)))
      ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ∞
      (fun w : ℝ × TangentBundle (𝓡 n) M =>
        (⟨w.1, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, ℝ)) (F := ℝ) (𝕜 := ℝ)
      (E := TangentSpace 𝓘(ℝ, ℝ))).comp contMDiff_fst
  have hlift : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n)))
      (P.prod 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) ∞
      (fun w : ℝ × TangentBundle (𝓡 n) M =>
        (⟨(w.1, w.2.proj), (0, w.2.snd)⟩ : TangentBundle P (ℝ × M))) :=
    contMDiff_equivTangentBundleProd_symm.comp (hz.prodMk contMDiff_snd)
  have htan := hPhi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    ((hT.prod hO).uniqueMDiffOn)
  have h := htan.comp
    (hlift.contMDiffOn (s := T ×ˢ {v : TangentBundle (𝓡 n) M | v.proj ∈ O}))
    (fun _ hw => ⟨hw.1, hw.2⟩)
  apply h.congr
  intro w hw
  change (⟨Phi (w.1, w.2.proj),
    mfderiv P (𝓡 k) Phi (w.1, w.2.proj) (0, w.2.snd)⟩ : TangentBundle (𝓡 k) N) =
      ⟨Phi (w.1, w.2.proj), mfderivWithin P (𝓡 k) Phi (T ×ˢ O)
        (w.1, w.2.proj) (0, w.2.snd)⟩
  have he := mfderivWithin_of_isOpen (I := P) (I' := 𝓡 k) (f := Phi)
    (x := (w.1, w.2.proj)) (hT.prod hO) ⟨hw.1, hw.2⟩
  exact congrArg (fun L : TangentSpace P (w.1, w.2.proj) →L[ℝ]
      TangentSpace (𝓡 k) (Phi (w.1, w.2.proj)) =>
    (⟨Phi (w.1, w.2.proj), L (0, w.2.snd)⟩ : TangentBundle (𝓡 k) N)) he.symm

end PoincareConjecture
