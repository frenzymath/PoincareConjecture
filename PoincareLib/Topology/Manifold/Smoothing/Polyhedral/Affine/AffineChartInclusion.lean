import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffineInverse
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Transporting the original chart compatibility into the cap ambient

Actual inverse and forward affine formulas along the same injective
inclusion identify the old overlap point. Affine composition transports
its original PL coordinate change, on exactly the new overlap. See
Hamilton 1976, p.66, Hudson 1969, pp.15--19 and M76 derivation346.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {X Y E F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The same injective inclusion and actual affine coordinate formulas
transport old compatibility. No old atlas on the cap is required.
See Hamilton p.66 and derivation346. -/
theorem affine_inclusion_transition_mem_piecewiseAffineGroupoid
    (j : Y → X) (hinj : Function.Injective j)
    (e f : OpenPartialHomeomorph Y E)
    (he : e.symm.trans f ∈ piecewiseAffineGroupoid E)
    (a b : E ≃ᴬ[ℝ] F) (c d : OpenPartialHomeomorph X F)
    (hc : ∀ p ∈ c.target, a.symm p ∈ e.target ∧ c.symm p = j (e.symm (a.symm p)))
    (hd : ∀ x ∈ d.source, ∃ y ∈ f.source, j y = x ∧ d x = b (f y)) :
    c.symm.trans d ∈ piecewiseAffineGroupoid F := by
  let T := e.symm.trans f
  let U := a.symm ⁻¹' T.source
  have hT : LocallyPiecewiseAffineOn T T.source :=
    (mem_piecewiseAffineGroupoid_iff_forward _).mp he
  have hpre : LocallyPiecewiseAffineOn (fun p => T (a.symm p)) U := by
    have h := hT.comp
      (locallyPiecewiseAffineOn_affine a.symm.toContinuousAffineMap isOpen_univ)
    simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap, univ_inter,
      Function.comp_def] using h
  have hPL : LocallyPiecewiseAffineOn (fun p => b (T (a.symm p))) U := by
    have h := (locallyPiecewiseAffineOn_affine b.toContinuousAffineMap isOpen_univ).comp hpre
    simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap, preimage_univ,
      inter_univ, Function.comp_def] using h
  have hpoint (p : F) (hp : p ∈ (c.symm.trans d).source) :
      p ∈ U ∧ (c.symm.trans d) p = b (T (a.symm p)) := by
    obtain ⟨hpt, hpval⟩ := hc p hp.1
    obtain ⟨y, hy, hjy, hdy⟩ := hd (c.symm p) hp.2
    have hyval : y = e.symm (a.symm p) := hinj (hjy.trans hpval)
    refine ⟨⟨hpt, ?_⟩, ?_⟩
    · change e.symm (a.symm p) ∈ f.source
      exact hyval ▸ hy
    · change d (c.symm p) = b (f (e.symm (a.symm p)))
      rw [hdy, hyval]
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  apply (hPL.mono (c.symm.trans d).open_source (fun p hp => (hpoint p hp).1)).congr
  intro p hp
  exact (hpoint p hp).2.symm

end OpenPartialHomeomorph
