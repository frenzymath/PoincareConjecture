import PoincareConjecture.Proofs.M35.CapGeometry.InitialAxialDifferential










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35



theorem initial_axial_patch_coefficient
    (g : RiemannianMetric 3 StandardCapSpace) {length : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch length x) (c l : ℝ) (hc : 0 < c) (hl : 0 < l)
    (hcl : c * l ≤ length) (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (hp : p.2 ∈ Ioo (-l) l) (i j : Fin 3) :
    roundCylinderTensorCoefficient
      (roundCylinderPullback g (N.axialRescale c l hc hl hcl).coordinate)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
      (if i = 2 then c else 1) * (if j = 2 then c else 1) *
        roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) (p.1, c * p.2) i j := by
  let ch := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let d := mfderiv (𝓡 2) (𝓡 2) ch.symm p.1
  let w (a : Fin 3) : RoundCylinderCoordinates :=
    (d (roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis a).2)
  have hw (a : Fin 3) : (d (roundCylinderCoordinateBasis a).1,
      c * (roundCylinderCoordinateBasis a).2) =
        (if a = 2 then c else 1) • w a := by
    fin_cases a <;> simp [w, roundCylinderCoordinateBasis]
  have hh := initial_axial_patch_pullback g N c l hc hl hcl (ch.symm p.1, p.2) hp
    (w i) (w j)
  change roundCylinderPullback g (N.axialRescale c l hc hl hcl).coordinate
    (ch.symm p.1, p.2) (w i) (w j) = _
  rw [hh]
  change roundCylinderPullback g N.coordinate (ch.symm p.1, c * p.2)
    (d (roundCylinderCoordinateBasis i).1, c * (roundCylinderCoordinateBasis i).2)
    (d (roundCylinderCoordinateBasis j).1, c * (roundCylinderCoordinateBasis j).2) = _
  rw [hw i, hw j]
  change g.inner (N.coordinate (ch.symm p.1, c * p.2))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate
      (ch.symm p.1, c * p.2) ((if i = 2 then c else 1) • w i))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate
      (ch.symm p.1, c * p.2) ((if j = 2 then c else 1) • w j)) = _
  rw [map_smul, map_smul, map_smul, smul_apply, map_smul]
  simp only [smul_eq_mul]
  dsimp only [roundCylinderTensorCoefficient, roundCylinderPullback, ch, w, d]
  ring



theorem initial_axial_model_error (Q c u v : ℝ) (hunit : Q * c ^ 2 = 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (i j : Fin 3) :
    Q * (if i = 2 then c else 1) * (if j = 2 then c else 1) *
        roundCylinderGram v (chartAt (EuclideanSpace ℝ (Fin 2)) q) (p.1, c * p.2) i j -
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
      (Q * (1 - v) - (1 - u)) *
        ((roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) -
          (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2) := by
  rw [roundCylinderGram_apply, roundCylinderGram_apply, roundCylinderGram_apply]
  fin_cases i <;> fin_cases j <;> simp [roundCylinderCoordinateBasis, pow_two]
  all_goals ring_nf at hunit ⊢
  all_goals nlinarith only [hunit]

end PoincareConjecture.M35
