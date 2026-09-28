import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Region

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

variable (h : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    (x : Real → Real)

def sliceParam (t y : Real) : E2 :=
  WithLp.toLp 2 ![x (h.symm (t - y^2)), y]

@[simp] theorem sliceParam_zero (t y : Real) :
    sliceParam h x t y 0 = x (h.symm (t - y^2)) := rfl

@[simp] theorem sliceParam_one (t y : Real) : sliceParam h x t y 1 = y := rfl

theorem contDiff_sliceParam (hx : ContDiff Real ∞ x) :
    ContDiff Real ∞ (fun ty : Real × Real => sliceParam h x ty.1 ty.2) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact hx.comp (h.symm.contDiff.comp (contDiff_fst.sub (contDiff_snd.pow 2)))
  · exact contDiff_snd

theorem sliceParam_isSmoothEmbedding (hx : ContDiff Real ∞ x) (t : Real) :
    _root_.Manifold.IsSmoothEmbedding 𝓘(Real, Real) (𝓡 2) ∞ (sliceParam h x t) := by
  have hs : ContDiff Real ∞ (sliceParam h x t) :=
    (contDiff_sliceParam h x hx).comp (contDiff_const.prodMk contDiff_id)
  have hsm : ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ (sliceParam h x t) := hs.contMDiff
  let P := EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)
  have hleft : Function.LeftInverse P (sliceParam h x t) := fun _ => rfl
  refine ⟨Poincare.Geometry.Manifold.isImmersion_of_injective_mfderiv hsm ?_,
    hleft.isEmbedding P.continuous hs.continuous⟩
  intro y
  have hcomp := mfderiv_comp y
    ((P.contMDiff (n := ∞)).mdifferentiable (by simp) (sliceParam h x t y))
    (hsm.mdifferentiable (by simp) y)
  rw [hleft.comp_eq_id, mfderiv_id] at hcomp
  have hproj (v : Real) :
      mfderiv (𝓡 2) 𝓘(Real, Real) P (sliceParam h x t y)
        (mfderiv 𝓘(Real, Real) (𝓡 2) (sliceParam h x t) y v) = v := by
    exact (congrArg (fun L => L v) hcomp).symm
  intro u v huv
  exact (hproj u).symm.trans
    ((congrArg (mfderiv (𝓡 2) 𝓘(Real, Real) P (sliceParam h x t y)) huv).trans
      (hproj v))

def sliceAtHeight (t : Real) (p : E2) : E3 := WithLp.toLp 2 ![p 0, p 1, t]

theorem sliceAtHeight_image_range (t : Real) :
    sliceAtHeight t '' range (sliceParam h x t) =
      roundedGraph h x ∩ {p : E3 | p 2 = t} := by
  ext p
  constructor
  · rintro ⟨q, ⟨y, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hp, ht⟩
    refine ⟨sliceParam h x t (p 1), ⟨p 1, rfl⟩, ?_⟩
    ext i
    fin_cases i
    · change x (h.symm (t - (p 1)^2)) = p 0
      change p 0 = x (h.symm (p 2 - (p 1)^2)) at hp
      rw [← ht]
      exact hp.symm
    · rfl
    · exact ht.symm

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing
