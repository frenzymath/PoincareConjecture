import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialEstimates.EndCoordinates

/-!
# Reflection in an exact cylindrical end

Morgan-Tian Theorem 12.5, p. 297. Compact doubles are glued using
reflection in the supplied cylinder height. The map and its derivative
are computed in the actual end coordinates, where reflection preserves
the literal cylinder metric. This supplies the metric-compatible overlap
for two truncated copies of the given cap.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- Reflection about height s/2 in the fixed cylinder
(Theorem 12.5 compact-double construction, p. 297). -/
def cylinderAxialReflection (s : ℝ) (z : StandardCylinderSpace) : StandardCylinderSpace :=
  (z.1, s - z.2)

/-- The cylinder reflection is smooth (Theorem 12.5, p. 297). -/
theorem cylinderAxialReflection_contMDiff (s : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (cylinderAxialReflection s) :=
  contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)

set_option backward.isDefEq.respectTransparency false in
/-- Reflection reverses precisely the axial tangent component
(Theorem 12.5 compact-double construction, p. 297). -/
theorem cylinderAxialReflection_mfderiv (s : ℝ) (z : StandardCylinderSpace)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderAxialReflection s) z v = (v.1, -v.2) := by
  have hs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun q : StandardCylinderSpace => s - q.2) z :=
    mdifferentiableAt_const.sub mdifferentiableAt_snd
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun q : StandardCylinderSpace => s - q.2) z =
        -mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd z := by
    change mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((fun _ : StandardCylinderSpace => s) - Prod.snd) z =
        -mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Prod.snd z
    rw [mvfderiv_sub mdifferentiableAt_const mdifferentiableAt_snd,
      mvfderiv_const, zero_sub]
  erw [cylinderAxialReflection, mfderiv_prodMk mdifferentiableAt_fst hs,
    hd, mfderiv_fst, mfderiv_snd]
  rfl

/-- Reflection preserves the literal cylinder metric at every model
time (Theorem 12.5 compact-double construction, p. 297). -/
theorem cylinderAxialReflection_metric (s t : ℝ) (z : StandardCylinderSpace)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    standardCylinderInner t (cylinderAxialReflection s z) (v.1, -v.2) (w.1, -w.2) =
      standardCylinderInner t z v w := by
  unfold standardCylinderInner cylinderAxialReflection
  dsimp only
  rw [neg_mul_neg]

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- Reflection expressed in the actual supplied cap coordinates
(Theorem 12.5 compact-double construction, p. 297). -/
def endAxialReflection (e : StandardCylindricalEnd g) (s : ℝ)
    (x : StandardCapSpace) : StandardCapSpace :=
  e.coordinate (cylinderAxialReflection s (e.inverse x))

/-- The reflected point has its prescribed end coordinates
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endAxialReflection_coordinate (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 ≤ z.2) :
    endAxialReflection e s (e.coordinate z) = e.coordinate (z.1, s - z.2) := by
  rw [endAxialReflection, e.coordinate_left_inverse ⟨mem_univ _, hz⟩]
  rfl

/-- Reflection is an involution wherever both heights are nonnegative
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endAxialReflection_involutive (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 ≤ z.2) (hsz : 0 ≤ s - z.2) :
    endAxialReflection e s (endAxialReflection e s (e.coordinate z)) = e.coordinate z := by
  rw [endAxialReflection_coordinate e s hz, endAxialReflection_coordinate e s hsz]
  simp

/-- The actual end reflection is smooth at points with two positive
heights (Theorem 12.5 compact-double construction, p. 297). -/
theorem endAxialReflection_contMDiffAt (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < s - z.2) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (endAxialReflection e s) (e.coordinate z) := by
  have hleft : e.inverse (e.coordinate z) = z :=
    e.coordinate_left_inverse ⟨mem_univ _, hz.le⟩
  have hc : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e.coordinate
      (cylinderAxialReflection s (e.inverse (e.coordinate z))) := by
    rw [hleft]
    exact end_coordinate_contMDiffAt e hsz
  have ht : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (cylinderAxialReflection s) (e.inverse (e.coordinate z)) :=
    (cylinderAxialReflection_contMDiff s).contMDiffAt
  exact hc.comp (e.coordinate z) (ht.comp (e.coordinate z) (end_inverse_contMDiffAt e hz))

set_option backward.isDefEq.respectTransparency false in
/-- The actual differential of end reflection reverses the axial part
between the inverse and direct coordinate derivatives (Theorem 12.5, p. 297). -/
theorem endAxialReflection_mfderiv (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < s - z.2)
    (u : TangentSpace (𝓡 3) (e.coordinate z)) :
    let v := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u
    mfderiv (𝓡 3) (𝓡 3) (endAxialReflection e s) (e.coordinate z) u =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate (z.1, s - z.2) (v.1, -v.2) := by
  dsimp only
  have hleft : e.inverse (e.coordinate z) = z :=
    e.coordinate_left_inverse ⟨mem_univ _, hz.le⟩
  have hi := (end_inverse_contMDiffAt e hz).mdifferentiableAt (by simp)
  have hs := (cylinderAxialReflection_contMDiff s).mdifferentiable (by simp)
  have hc : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
      (cylinderAxialReflection s (e.inverse (e.coordinate z))) := by
    rw [hleft]
    exact (end_coordinate_contMDiffAt e hsz).mdifferentiableAt (by simp)
  change mfderiv (𝓡 3) (𝓡 3)
    (e.coordinate ∘ (cylinderAxialReflection s ∘ e.inverse)) (e.coordinate z) u = _
  have ht : MDifferentiableAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderAxialReflection s ∘ e.inverse) (e.coordinate z) :=
    (hs (e.inverse (e.coordinate z))).comp (e.coordinate z) hi
  erw [mfderiv_comp (e.coordinate z) hc ht,
    mfderiv_comp (e.coordinate z) (hs (e.inverse (e.coordinate z))) hi]
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
    (cylinderAxialReflection s (e.inverse (e.coordinate z)))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderAxialReflection s) (e.inverse (e.coordinate z))
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u)) = _
  erw [cylinderAxialReflection_mfderiv]
  congr 2
  exact congrArg (cylinderAxialReflection s) hleft

set_option backward.isDefEq.respectTransparency false in
/-- End reflection preserves the actual supplied metric on its valid
positive-height overlap (Theorem 12.5 compact-double construction, p. 297). -/
theorem endAxialReflection_metric (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < s - z.2)
    (u v : TangentSpace (𝓡 3) (e.coordinate z)) :
    g.inner (e.coordinate z) u v =
      g.inner (endAxialReflection e s (e.coordinate z))
        (mfderiv (𝓡 3) (𝓡 3) (endAxialReflection e s) (e.coordinate z) u)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialReflection e s) (e.coordinate z) v) := by
  erw [endAxialReflection_coordinate e s hz.le,
    endAxialReflection_mfderiv e s hz hsz, endAxialReflection_mfderiv e s hz hsz,
    e.metric_pullback _ hsz.le, end_inverse_metric e hz]
  exact (cylinderAxialReflection_metric s 0 z _ _).symm

end PoincareMT.M34
