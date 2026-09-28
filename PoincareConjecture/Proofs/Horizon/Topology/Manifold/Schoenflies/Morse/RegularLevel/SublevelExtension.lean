import PoincareConjecture.Proofs.Horizon.Topology.Connected.SublevelNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sublevel.LowerSide
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_height_extension_above_sublevel_component
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (p : S2) (b : Real)
    (hregular : ∀ q, h q = b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0) :
    ∃ k : S2 → Real, ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ k ∧
      (∀ᶠ x in 𝓝ˢ (closure (connectedComponentIn (h ⁻¹' Iio b) p)), k x = h x) ∧
      ∀ x ∉ closure (connectedComponentIn (h ⁻¹' Iio b) p), b < k x := by
  let : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2
  obtain ⟨U, hU, hKU, hUK⟩ :=
    Poincare.Topology.exists_open_neighborhood_sublevel_component hh.continuous p b
      (fun q hq => by
        simpa only [hq] using Poincare.Geometry.Manifold.hasConnectedLowerSide_of_regular
          hh isOpen_univ (mem_univ q) (hregular q hq))
  obtain ⟨χ, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓡 2)
      (s := closure (connectedComponentIn (h ⁻¹' Iio b) p)) (t := U)
      isClosed_closure (by simpa only [hU.interior_eq] using hKU) (n := ⊤)
  let k : S2 → Real := fun x => χ x * h x + (1 - χ x) * (b + 1)
  refine ⟨k, (χ.contMDiff.mul hh).add
    ((contMDiff_const.sub χ.contMDiff).mul contMDiff_const), ?_, ?_⟩
  · filter_upwards [hχone] with x hx
    simp only [k, hx, one_mul, sub_self, zero_mul, add_zero]
  · intro x hx
    by_cases hxU : x ∈ U
    · have hbx : b < h x := lt_of_not_ge (fun hxb => hx (hUK ⟨hxU, hxb⟩))
      have hnonneg := (hχrange x).1
      have hle := (hχrange x).2
      by_cases hzero : χ x = 0
      · simp only [k, hzero, zero_mul, sub_zero, one_mul, zero_add]
        linarith
      · have hpos : 0 < χ x := lt_of_le_of_ne hnonneg (Ne.symm hzero)
        have hp := mul_pos hpos (sub_pos.mpr hbx)
        dsimp [k]
        nlinarith
    · simp only [k, hχzero x hxU, zero_mul, sub_zero, one_mul, zero_add]
      linarith

end Poincare.Manifold.Schoenflies
