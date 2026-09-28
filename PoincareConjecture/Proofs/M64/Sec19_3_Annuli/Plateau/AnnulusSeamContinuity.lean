import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamPowerGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakRepresentative
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyLocalRepresentative













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "v" => m64AnnulusSeamTranslation



theorem m64SeamRepresentative_translation
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {F f : LoopPlane → M} (hF : ContinuousOn F O)
    (hfae : F =ᵐ[volume.restrict O] m64AnnulusSeamExtend f) :
    ∀ p ∈ m64AnnulusSeamLeft, F (v + p) = F p := by
  have hright : F =ᵐ[volume.restrict S] f := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset m64AnnulusSeam_rect_subset hfae,
      ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
    exact hp.trans (m64AnnulusSeamExtend_right f hpS)
  have hshift := m64AnnulusSeam_translation_measurePreserving.quasiMeasurePreserving.ae hright
  have hleft := ae_restrict_of_ae_restrict_of_subset m64AnnulusSeam_left_subset hfae
  have hae : (fun p => F (v + p)) =ᵐ[volume.restrict m64AnnulusSeamLeft] F := by
    filter_upwards [hshift, hleft, ae_restrict_mem m64AnnulusSeamLeft_isOpen.measurableSet]
      with p hp hq hpL
    exact hp.trans ((m64AnnulusSeamExtend_left f hpL).symm.trans hq.symm)
  have hshiftC : ContinuousOn (fun p => F (v + p)) m64AnnulusSeamLeft :=
    hF.comp (continuous_const.add continuous_id).continuousOn fun p hp =>
      m64AnnulusSeam_rect_subset hp
  exact Measure.eqOn_open_of_ae_eq hae m64AnnulusSeamLeft_isOpen hshiftC
    (hF.mono m64AnnulusSeam_left_subset)

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)




theorem M64ObservedWeakAnnulus.seam_continuous_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q w, 0 ≤ Q q w w)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (w : E), w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖w‖ ^ 2 ≤ C * Q q w w)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      ContinuousOn B.map O ∧ B.map =ᵐ[volume.restrict O] m64AnnulusSeamExtend A.map ∧
      B.map =ᵐ[volume.restrict S] A.map ∧
      (∀ p ∈ m64AnnulusSeamLeft, B.map (v + p) = B.map p) ∧
      B.column = A.column ∧ B.energy Q = A.energy Q ∧
      ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, B.energy Q ≤ W.energy Q := by
  have hgrowth (a : LoopPlane) (ha : a ∈ O) :=
    A.seam_local_column_power_growth g he hei hread Q hQ hpos hC hcoercive hmin a ha
  obtain ⟨U, hU, hUae⟩ := m64Morrey_local_representative A.seam_extension_memLp.1
    A.seam_extension_memLp.2 A.seam_extension_weak_partial (by
      intro a ha
      obtain ⟨rho, hrho, hsub, K, hK, beta, hbeta, hg⟩ := hgrowth a ha
      exact ⟨rho, hrho, hsub, K, hK, beta, hbeta, fun i b hb r hr => hg b hb r hr i⟩)
  obtain ⟨F, hF, hFae, -⟩ := m64ClosedEmbedding_continuous_representative hei
    m64AnnulusSeamDomain_isOpen (m64AnnulusSeamExtend A.map) U hU hUae
  have hFaeS : F =ᵐ[volume.restrict S] A.map := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset m64AnnulusSeam_rect_subset hFae,
      ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
    exact hp.trans (m64AnnulusSeamExtend_right A.map hpS)
  have hshift := m64SeamRepresentative_translation hF hFae
  obtain ⟨B, hmap, hcolumn, henergy⟩ := A.with_map_ae F hFaeS
  refine ⟨B, hmap ▸ hF, hmap ▸ hFae, hmap ▸ hFaeS, hmap ▸ hshift, hcolumn, henergy Q, ?_⟩
  intro W
  rw [henergy]
  exact hmin W

end PoincareConjecture
