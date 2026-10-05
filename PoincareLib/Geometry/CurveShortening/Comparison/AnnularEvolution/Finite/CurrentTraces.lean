import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Finite.MotionTangent
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Finite.ParameterVelocity

/-! Continuous conormal currents on the actual closed rectangle.
Only within derivatives are used on its boundary. Source: MT Lemma
19.15, pp. 447-449; finite-conormal-variation derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The genuine time velocity paired with the within spatial column at the base annulus.
This supplies the actual boundary trace. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
def m64FiniteAnnulusCurrent (g : RiemannianMetric n M)
    (v : ℝ → LoopPlane → M) (i : Fin 2) (p : LoopPlane) : ℝ :=
  g.inner (v 0 p) (curveVelocity (fun s => v s p) 0)
    (mfderivWithin (𝓡 2) (𝓡 n) (v 0) m64AnnulusDomain p
      (EuclideanSpace.basisFun (Fin 2) ℝ i))

/-- A C1 base map and continuous genuine velocity give continuous current traces on every
face of the closed annulus. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16,
pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64FiniteAnnulusCurrent_continuousOn
    (g : RiemannianMetric n M) {v : ℝ → LoopPlane → M}
    (hbase : ContMDiffOn (𝓡 2) (𝓡 n) 1 (v 0) m64AnnulusDomain)
    (hV : ContinuousOn (fun p =>
      (⟨v 0 p, curveVelocity (fun s => v s p) 0⟩ : TangentBundle (𝓡 n) M))
      m64AnnulusDomain) (i : Fin 2) :
    ContinuousOn (m64FiniteAnnulusCurrent g v i) m64AnnulusDomain := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact hV.inner_bundle (m64AnnulusWithinColumn_continuousOn hbase i)

/-- On the open rectangle the within current is the ordinary intrinsic time-velocity
pairing. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64FiniteAnnulusCurrent_eq_pairing
    (g : RiemannianMetric n M) (v : ℝ → LoopPlane → M) (i : Fin 2)
    {p : LoopPlane} (hp : p ∈ interior m64AnnulusDomain) :
    m64FiniteAnnulusCurrent g v i p =
      g.inner (v 0 p) (curveVelocity (fun s => v s p) 0)
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  rw [m64FiniteAnnulusCurrent, mfderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)]

/-- Interior smoothness of the base and C1 of the genuine velocity make the actual current
differentiable inside the rectangle. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary
19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64FiniteAnnulusCurrent_differentiableAt
    (g : RiemannianMetric n M) {v : ℝ → LoopPlane → M} {p : LoopPlane}
    (hp : p ∈ interior m64AnnulusDomain)
    (hbase : ContMDiffAt (𝓡 2) (𝓡 n) ∞ (v 0) p)
    (hV : ContMDiffAt (𝓡 2) ((𝓡 n).prod (𝓡 n)) 1 (fun q =>
      (⟨v 0 q, curveVelocity (fun s => v s q) 0⟩ : TangentBundle (𝓡 n) M)) p)
    (i : Fin 2) : DifferentiableAt ℝ (m64FiniteAnnulusCurrent g v i) p := by
  have hvec : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q : LoopPlane => (⟨q, EuclideanSpace.basisFun (Fin 2) ℝ i⟩ :
        TangentBundle (𝓡 2) LoopPlane)) p := by
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa using contMDiffAt_const (c := EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hcol := (hbase.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hvec hbase
  have hm := (((g.contMDiff (v 0 p)).comp p hbase).of_le (by simp)).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hV (hcol.of_le (by simp))
  have hs : ContDiffAt ℝ 1 (fun q => g.inner (v 0 q)
      (curveVelocity (fun s => v s q) 0)
      (mfderiv (𝓡 2) (𝓡 n) (v 0) q (EuclideanSpace.basisFun (Fin 2) ℝ i))) p :=
    contMDiffAt_iff_contDiffAt.mp (Bundle.contMDiffAt_totalSpace.mp hm).2
  apply (hs.congr_of_eventuallyEq ?_).differentiableAt one_ne_zero
  filter_upwards [isOpen_interior.mem_nhds hp] with q hq
  exact m64FiniteAnnulusCurrent_eq_pairing g v i hq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual C1 parameter map supplies a C1 time-velocity section on the whole closed
rectangle. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64ParameterAnnulus_timeVelocity_contMDiffOn
    {Phi : ℝ × E → M} {T : Set ℝ} {O : Set E}
    (hT : IsOpen T) (hO : IsOpen O)
    (hPhi : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ Phi (T ×ˢ O))
    {h : LoopPlane → E} (hh : ContDiffOn ℝ 1 h m64AnnulusDomain)
    (hmap : MapsTo h m64AnnulusDomain O) {t : ℝ} (ht : t ∈ T) :
    ContMDiffOn (𝓡 2) ((𝓡 n).prod (𝓡 n)) 1 (fun p =>
      (⟨Phi (t, h p), curveVelocity (fun s => Phi (s, h p)) t⟩ :
        TangentBundle (𝓡 n) M)) m64AnnulusDomain := by
  intro p hp
  have hV := (m64ParameterMotion_timeVelocity_contMDiffAt (hT.prod hO) hPhi
    (show (t, h p) ∈ T ×ˢ O from ⟨ht, hmap hp⟩)).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)
  exact hV.comp_contMDiffWithinAt p
    ((contDiffWithinAt_const.prodMk (hh p hp)).contMDiffWithinAt)

end PoincareMT
