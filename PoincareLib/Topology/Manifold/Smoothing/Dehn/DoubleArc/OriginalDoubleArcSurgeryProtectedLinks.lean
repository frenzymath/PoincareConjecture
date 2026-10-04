import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleArc.OriginalDoubleArcSurgeryOldGerms
import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleArc.OriginalDoubleArcSurgeryStep
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLInitialSegment
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.RadialSegmentGerms
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CentralLinkSigns

/-!
# Actual old protected links from the retained history

The original marked assembly is constructed once. A finite exceptional
target set isolates the selected operation, so every protected zero
point is an old ordinary double point. Complete inverse windows identify
the same double relation independently of the ordering of their sheets.
The centered old axis has two initial affine inverse segments, giving
the whole zero section of the actual protected vertex link. The two
ambient half-boxes give both strict signs on that same old link.
This is the old-link application in Dehn039 and signed-tube Step A.5.
-/

set_option autoImplicit false

open Set Metric Geometry Topology Filter unitInterval
open scoped Topology
open PoincareMT.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 1600000 in
-- Keep the actual initial history, operation and inverse-axis calculation in one proof.
/-- The original disk constructs a fixed protected refinement whose
every interior protected zero vertex has exactly two whole link zeros
and both strict height signs. The same refinement and sign margin
precede every motion size. The moved ambient crossed chart remains
separate. See Dehn039 section4. -/
theorem Step.exists_original_protected_link_sections
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareMT.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup) :
    ∃ (initial : StageMarkedDisk t R Fmark base Jgroup)
      (eta : old.rim.Homotopy initial.rim),
      initial.basepath = old.basepath.trans (eta.evalAt squareRimBase) ∧
      ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
        step.projection (step.inclusion (initial.map a)) =
          step.projection (step.inclusion (initial.map b)) →
        ∀ U : Set s.Carrier, IsOpen U →
          step.projection (step.inclusion (initial.map a)) ∈ U →
          ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
            (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
            (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
            (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
            initial.map a ∈ w.left.source ∧ initial.map b ∈ w.right.source ∧
            step.projection (step.inclusion (initial.map a)) ∈ Q.source ∧
            Q (step.projection (step.inclusion (initial.map a))) = 0 ∧
            Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
            (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
            (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
              (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
            (∀ y ∈ Q.source,
              y ∈ (step.projection ∘ step.inclusion) '' (initial.map '' D ∩ w.left.source) ↔
                (c (Q y)).2 = 0) ∧
            J.faces.Finite ∧ J.space ⊆ Q.target ∧ (0 : V3) ∈ interior J.space ∧
            0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
            P.space = (w.right.trans Q) ''
              (initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
            P₀.space = P.space \ ball (0 : V3) ρ ∧
            R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧ K.space = P.space ∧
            K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
            (∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior (q '' P.space)) ∧
            (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
              (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
            (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
              ∃ T : OpenPartialHomeomorph V3 C3,
                (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
                LocallyPiecewiseAffineOn T.symm T.target ∧
                (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
                  (T z).1.1 = 0) ∧
                ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
            (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
              v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
              v ∈ closure (K.space ∩ {z | (c z).2 < 0})) ∧
            (∀ v ∈ K₀.vertices, v ∈ interior J.space → (c v).2 = 0 →
              ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
              (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
              ∃ z ∈ (K.link v).space, (c z).2 < 0) ∧
            (∀ v ∈ K.vertices, v ∈ interior J.space →
              ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
                T.HasSimplicialEdges ∧ T.boundary ℝ = (K.link v).space) ∧
            L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
            0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
            ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
              R₀.AffineOnFaces (H.map 1) ∧
              (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
                (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
                ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
              (∀ v ∈ K.vertices,
                (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
              (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
                face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
              (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
                affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
                  Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
                    (convexHull ℝ (other : Set V3))) ∧
              ∃ Kamb Knew : SimplicialComplex ℝ V3,
                Kamb.faces.Finite ∧ Kamb.space = J.space ∧ Knew ≤ Kamb ∧
                Knew.space = H.map 1 '' P.space ∧ K₀ ≤ Knew ∧
                Knew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
                InjOn (q ∘ (H.map 1).symm) Knew.space ∧
                (∀ v ∈ K.vertices,
                  (Knew.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
                  (Knew.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
                (∀ v ∈ K.vertices, v ∈ interior J.space →
                  ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
                    T.HasSimplicialEdges ∧ T.boundary ℝ = (Knew.link (H.map 1 v)).space) ∧
              ∃ (G : I → t.Carrier ≃ₜ t.Carrier)
                (new : StageMarkedDisk t R Fmark base Jgroup),
                Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
                Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
                (∀ x, G 0 x = x) ∧
                (∀ u, EqOn (G u)
                  ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
                    (w.right.trans Q).source) ∧
                (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
                (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' P₀.space)) ∧
                (∀ u, EqOn (G u) id w.left.source) ∧
                (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
                (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
                (∀ u k l, (t.charts k).symm.trans
                  ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
                (∀ x, new.map x = G 1 (initial.map x)) ∧ new.rim = initial.rim ∧
                HEq new.basepath initial.basepath ∧
                (∀ x : Rim, new.map x = initial.map x) ∧
                (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
                  H.map 1 '' P.space ∧
                ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
                  (first : Z.space ≃ₜ E.space),
                  Z.faces.Finite ∧ E.faces.Finite ∧
                  Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
                    step.projection (step.inclusion (new.map z.1)) =
                      step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
                  E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
                    step.projection (step.inclusion (new.map x)) =
                      step.projection (step.inclusion (new.map y))} ∧
                  first.IsFinitePL ∧ first.symm.IsFinitePL ∧
                  ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  have axis_count (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
      (hzero : (0 : V3) ∈ K.vertices) (ell : V3 →ₗ[ℝ] ℝ)
      (H : OpenPartialHomeomorph V3 C3) (hsource : (0 : V3) ∈ H.source)
      (hcenter : H 0 = 0) (hinverse : LocallyPiecewiseAffineOn H.symm H.target)
      (hsection : ∀ x ∈ H.source, x ∈ K.space ∩ {z | ell z = 0} ↔
        (H x).1.1 = 0 ∧ (H x).2 = 0) :
      ((K.link 0).space ∩ {x | ell x = 0}).ncard = 2 := by
    have htarget : (0 : C3) ∈ H.target := hcenter ▸ H.map_source hsource
    have hinvzero : H.symm 0 = 0 := by
      rw [← hcenter]
      exact H.left_inv hsource
    obtain ⟨N, hN, hzeroN, hNH, hNaff⟩ := hinverse 0 htarget
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hzeroN
    let d := r / 2
    have hd : 0 < d := half_pos hr
    have hdr : d < r := half_lt_self hr
    let axis : ℝ →L[ℝ] C3 :=
      { toLinearMap :=
          { toFun := fun z => ((0, z), 0)
            map_add' := by intros; ext <;> simp
            map_smul' := by intros; ext <;> simp }
        cont := by fun_prop }
    have hnorm (z : ℝ) : ‖axis z‖ = |z| := by
      simp [axis, Prod.norm_def, Real.norm_eq_abs]
    have small (k : ℝ) (hk : |k| = d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
        axis (k * u) ∈ N.space := by
      apply interior_subset (hball ?_)
      rw [mem_ball, dist_zero_right, hnorm, abs_mul, hk, abs_of_nonneg hu.1]
      exact (mul_le_of_le_one_right hd.le hu.2).trans_lt hdr
    have initial (k : ℝ) (hk : |k| = d) :
        ∃ δ ∈ Ioc (0 : ℝ) 1, ∃ v : V3, v ≠ 0 ∧
          ∀ u ∈ Icc (0 : ℝ) 1,
            u • v ∈ H.source ∧ H (u • v) = axis (k * δ * u) := by
      let a : ℝ →ᴬ[ℝ] C3 :=
        axis.toContinuousAffineMap.comp (k • ContinuousAffineMap.id ℝ ℝ)
      have ha : MapsTo a (Icc (0 : ℝ) 1) N.space := fun _ hu => small k hk hu
      obtain ⟨δ, hδ, A, hA⟩ :=
        (hNaff.finitePiecewiseAffineOn hN).exists_initial_affine_segment a ha
      have hA0 : A 0 = 0 := by
        have h := hA ⟨le_rfl, hδ.1.le⟩
        change H.symm (axis (k * 0)) = A 0 at h
        rw [mul_zero, map_zero, hinvzero] at h
        exact h.symm
      have hlin (u : ℝ) : A u = u • A 1 := by
        have h := A.toAffineMap.apply_lineMap (0 : ℝ) 1 u
        change A (AffineMap.lineMap 0 1 u) = AffineMap.lineMap (A 0) (A 1) u at h
        simpa [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_module', hA0] using h
      let v := δ • A 1
      have hmap (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
          u • v ∈ H.source ∧ H (u • v) = axis (k * δ * u) := by
        have hdu : δ * u ∈ Icc (0 : ℝ) δ :=
          ⟨mul_nonneg hδ.1.le hu.1, mul_le_of_le_one_right hδ.1.le hu.2⟩
        have hdu1 : δ * u ∈ Icc (0 : ℝ) 1 := ⟨hdu.1, hdu.2.trans hδ.2⟩
        have hval : H.symm (axis (k * δ * u)) = u • v := by
          have h := (hA hdu).trans (hlin (δ * u))
          change H.symm (axis (k * (δ * u))) = (δ * u) • A 1 at h
          simpa only [v, smul_smul, mul_assoc, mul_comm δ u] using h
        have hpoint : axis (k * δ * u) ∈ H.target := by
          apply hNH
          simpa only [mul_assoc] using small k hk hdu1
        exact ⟨hval ▸ H.map_target hpoint, by rw [← hval]; exact H.right_inv hpoint⟩
      have hv : v ≠ 0 := by
        intro hv0
        have h := (hmap 1 (by simp)).2
        rw [one_smul, hv0, hcenter, mul_one] at h
        have hkδ : k * δ = 0 := (congrArg (fun x : C3 => x.1.2) h).symm
        have hk0 : k ≠ 0 := by
          intro hk0
          have hd0 : d = 0 := by simpa only [hk0, abs_zero] using hk.symm
          exact hd.ne' hd0
        exact (mul_ne_zero hk0 hδ.1.ne') hkδ
      exact ⟨δ, hδ, v, hv, hmap⟩
    obtain ⟨a, ha, u, hu, hplus⟩ := initial d (abs_of_pos hd)
    obtain ⟨b, hb, v, hv, hminus⟩ := initial (-d) (by rw [abs_neg, abs_of_pos hd])
    have hda : 0 < d * a := mul_pos hd ha.1
    have hdb : 0 < d * b := mul_pos hd hb.1
    have radial (w : V3) {x : V3} (hx : x ∈ segment ℝ 0 w) :
        ∃ u ∈ Icc (0 : ℝ) 1, u • w = x := by
      obtain ⟨u, hu, hux⟩ := (segment_eq_image_lineMap ℝ (0 : V3) w).subset hx
      exact ⟨u, hu, by simpa [AffineMap.lineMap_apply_module] using hux⟩
    have hinter : segment ℝ 0 u ∩ segment ℝ 0 v ⊆ {0} := by
      intro x hx
      obtain ⟨i, hi, hix⟩ := radial u hx.1
      obtain ⟨j, hj, hjx⟩ := radial v hx.2
      have heq : H (i • u) = H (j • v) := congrArg H (hix.trans hjx.symm)
      rw [(hplus i hi).2, (hminus j hj).2] at heq
      have hcoeff : d * a * i = -d * b * j := congrArg (fun z : C3 => z.1.2) heq
      have hprod : d * a * i = 0 := by
        apply le_antisymm
        · rw [hcoeff]
          simp only [neg_mul]
          exact neg_nonpos.mpr (mul_nonneg hdb.le hj.1)
        · exact mul_nonneg hda.le hi.1
      have hi0 := (mul_eq_zero.mp hprod).resolve_left hda.ne'
      exact hix.symm.trans (by rw [hi0, zero_smul])
    let O : Set C3 := {x | -(d * b) < x.1.2 ∧ x.1.2 < d * a}
    have hO : IsOpen O :=
      (isOpen_lt continuous_const (continuous_snd.comp continuous_fst)).inter
        (isOpen_lt (continuous_snd.comp continuous_fst) continuous_const)
    have hzeroO : H 0 ∈ O := by
      rw [hcenter]
      exact ⟨neg_neg_of_pos hdb, hda⟩
    have hlocal : ∀ᶠ x in 𝓝 (0 : V3), x ∈ K.space ∩ {z | ell z = 0} ↔
        x ∈ segment ℝ 0 u ∪ segment ℝ 0 v := by
      filter_upwards [(H.isOpen_inter_preimage hO).mem_nhds ⟨hsource, hzeroO⟩] with x hx
      constructor
      · intro hsectionx
        have haxes := (hsection x hx.1).mp hsectionx
        have hxaxis : H x = axis (H x).1.2 := Prod.ext (Prod.ext haxes.1 rfl) haxes.2
        by_cases hn : 0 ≤ (H x).1.2
        · let t := (H x).1.2 / (d * a)
          have ht : t ∈ Icc (0 : ℝ) 1 :=
            ⟨div_nonneg hn hda.le, (div_le_one hda).mpr hx.2.2.le⟩
          have htx : t • u = x := H.injOn (hplus t ht).1 hx.1 (by
            rw [(hplus t ht).2, hxaxis]
            dsimp only [t]
            rw [mul_div_cancel₀ _ hda.ne'])
          exact Or.inl (htx ▸ (convex_segment (0 : V3) u).smul_mem_of_zero_mem
            (left_mem_segment ℝ 0 u) (right_mem_segment ℝ 0 u) ht)
        · have hn' : (H x).1.2 ≤ 0 := le_of_not_ge hn
          let t := -(H x).1.2 / (d * b)
          have ht : t ∈ Icc (0 : ℝ) 1 :=
            ⟨div_nonneg (neg_nonneg.mpr hn') hdb.le,
              (div_le_one hdb).mpr (by linarith [hx.2.1])⟩
          have htx : t • v = x := H.injOn (hminus t ht).1 hx.1 (by
            rw [(hminus t ht).2, hxaxis]
            dsimp only [t]
            rw [neg_mul, neg_mul, mul_div_cancel₀ _ hdb.ne', neg_neg])
          exact Or.inr (htx ▸ (convex_segment (0 : V3) v).smul_mem_of_zero_mem
            (left_mem_segment ℝ 0 v) (right_mem_segment ℝ 0 v) ht)
      · intro hsegment
        apply (hsection x hx.1).mpr
        rcases hsegment with hxu | hxv
        · obtain ⟨i, hi, rfl⟩ := radial u hxu
          rw [(hplus i hi).2]
          exact ⟨rfl, rfl⟩
        · obtain ⟨i, hi, rfl⟩ := radial v hxv
          rw [(hminus i hi).2]
          exact ⟨rfl, rfl⟩
    exact K.ncard_link_zero_of_local_segments hK hzero ell hu hv hinter hlocal
  have surface_signs (K : SimplicialComplex ℝ V3) (ell : V3 →L[ℝ] ℝ)
      (w : V3) (hw : ell w = 1) (H : OpenPartialHomeomorph V3 C3)
      (hsource : (0 : V3) ∈ H.source) (hcenter : H 0 = 0)
      (hflat : ∀ x ∈ H.source, ell x = 0 ↔ (H x).2 = 0)
      (hsheet : ∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) :
      (0 : V3) ∈ closure (K.space ∩ {x | 0 < ell x}) ∧
        (0 : V3) ∈ closure (K.space ∩ {x | ell x < 0}) := by
    have htarget : (0 : C3) ∈ H.target := hcenter ▸ H.map_source hsource
    have hinvzero : H.symm 0 = 0 := by
      rw [← hcenter]
      exact H.left_inv hsource
    have positive (L : V3 →L[ℝ] ℝ) (w : V3) (hw : L w = 1)
        (hflat : ∀ x ∈ H.source, L x = 0 ↔ (H x).2 = 0) :
        (0 : V3) ∈ closure (K.space ∩ {x | 0 < L x}) := by
      apply _root_.mem_closure_iff.mpr
      intro N hN hzeroN
      have hN' := H.symm.isOpen_inter_preimage hN
      have hzeroN' : (0 : C3) ∈ H.target ∩ H.symm ⁻¹' N := by
        refine ⟨htarget, ?_⟩
        change H.symm 0 ∈ N
        rw [hinvzero]
        exact hzeroN
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN' 0 hzeroN'
      let I₀ := Ioo (-r) r
      let P := (I₀ ×ˢ I₀) ×ˢ I₀
      have hPopen : IsOpen P := (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo
      have hzeroP : (0 : C3) ∈ P := by
        have hz : (0 : ℝ) ∈ I₀ := ⟨neg_neg_of_pos hr, hr⟩
        exact ⟨⟨hz, hz⟩, hz⟩
      have hP (z : C3) (hz : z ∈ P) : z ∈ H.target ∩ H.symm ⁻¹' N := by
        apply hball
        rw [mem_ball, dist_zero_right, Prod.norm_def, Prod.norm_def]
        simp only [Real.norm_eq_abs, max_lt_iff, abs_lt]
        exact hz
      have hpre : H.source ∩ H ⁻¹' P ∈ 𝓝 (0 : V3) := by
        apply (H.isOpen_inter_preimage hPopen).mem_nhds
        refine ⟨hsource, ?_⟩
        change H 0 ∈ P
        rw [hcenter]
        exact hzeroP
      obtain ⟨a, ha, haw⟩ := Set.exists_pos_smul_mem_of_mem_nhds hpre w
      have hawpos : 0 < L (a • w) := by rw [map_smul, hw, smul_eq_mul, mul_one]; exact ha.1
      let f : C3 → ℝ := L ∘ H.symm
      have hf : ContinuousOn f P :=
        L.continuous.comp_continuousOn (H.continuousOn_symm.mono fun z hz => (hP z hz).1)
      have hfv : 0 < f (H (a • w)) := by
        change 0 < L (H.symm (H (a • w)))
        rw [H.left_inv haw.1]
        exact hawpos
      have hnz : (H (a • w)).2 ≠ 0 := fun h =>
        hawpos.ne' ((hflat _ haw.1).mpr h)
      have nonzero (z : C3) (hz : z ∈ P) (hz0 : z.2 ≠ 0) : f z ≠ 0 := by
        intro heq
        have h := (hflat _ (H.map_target (hP z hz).1)).mp heq
        rw [H.right_inv (hP z hz).1] at h
        exact hz0 h
      rcases lt_or_gt_of_ne hnz with hneg | hpos
      · let z : C3 := ((0, 0), -(r / 2))
        have hz : z ∈ (I₀ ×ˢ I₀) ×ˢ Ioo (-r) 0 := by
          dsimp only [z, I₀]
          exact ⟨hzeroP.1, ⟨by linarith, by linarith⟩⟩
        have hsub : (I₀ ×ˢ I₀) ×ˢ Ioo (-r) 0 ⊆ P :=
          fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hr⟩
        have hzpos : 0 < f z :=
          ((isPreconnected_Ioo.prod isPreconnected_Ioo).prod isPreconnected_Ioo).lt_of_ne
            (hf.mono hsub) (fun z hz => nonzero z (hsub hz) hz.2.2.ne)
            ⟨H (a • w), ⟨haw.2.1, haw.2.2.1, hneg⟩, hfv⟩ hz
        refine ⟨H.symm z, (hP z (hsub hz)).2, ?_, hzpos⟩
        apply (hsheet _ (H.map_target (hP z (hsub hz)).1)).mpr
        rw [H.right_inv (hP z (hsub hz)).1]
      · let z : C3 := ((0, 0), r / 2)
        have hz : z ∈ (I₀ ×ˢ I₀) ×ˢ Ioo 0 r := by
          dsimp only [z, I₀]
          exact ⟨hzeroP.1, ⟨half_pos hr, half_lt_self hr⟩⟩
        have hsub : (I₀ ×ˢ I₀) ×ˢ Ioo 0 r ⊆ P :=
          fun z hz => ⟨hz.1, (neg_neg_of_pos hr).trans hz.2.1, hz.2.2⟩
        have hzpos : 0 < f z :=
          ((isPreconnected_Ioo.prod isPreconnected_Ioo).prod isPreconnected_Ioo).lt_of_ne
            (hf.mono hsub) (fun z hz => nonzero z (hsub hz) hz.2.1.ne')
            ⟨H (a • w), ⟨haw.2.1, hpos, haw.2.2.2⟩, hfv⟩ hz
        refine ⟨H.symm z, (hP z (hsub hz)).2, ?_, hzpos⟩
        apply (hsheet _ (H.map_target (hP z (hsub hz)).1)).mpr
        rw [H.right_inv (hP z (hsub hz)).1]
    have hpos := positive ell w hw hflat
    have hneg := positive (-ell) (-w)
      (by simp only [neg_apply, map_neg, neg_neg, hw])
      (fun x hx => by simpa only [neg_apply, neg_eq_zero] using hflat x hx)
    exact ⟨hpos, by simpa only [neg_apply, neg_pos] using hneg⟩
  obtain ⟨initial, eta, Ks, As, hpath, _, _, _, _, _,
    n, order, Pseq, boundary, Qseq, Bseq, Jseq, Useq, states, motions,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    Z, G, first, E, _, _, _, _, _, _, _, _, _, hE, _, hcross⟩ :=
    step.exists_original_old_crossing_assembly he hF hopen old
  let p := step.projection ∘ step.inclusion
  let lower := p ∘ initial.map
  let bad := (fun z : V2 × V2 => lower z.1) '' E
  have hbad : bad.Finite := hE.image _
  refine ⟨initial, eta, hpath, ?_⟩
  intro a b hab haint hpair U hU haU
  let W := U \ (bad \ {lower a})
  have hW : IsOpen W := hU.sdiff (hbad.subset sdiff_subset).isClosed
  have haW : lower a ∈ W := ⟨haU, fun h => h.2 rfl⟩
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQW, hQw, hQPL, hbranches, hplane,
    hJ, _hcv, hJQ, hzeroJ, hρ, hball, _hP, _hP₀, hPs, hP₀s,
    _hbB, _hzeroP, _hq, hqi, hqint, hR₀, hR₀J, hKR, hKs, hqK,
    hK₀K, hK₀s, hL, hLs, hlinks, hwhole, hδ, hmargin, hmotions⟩ :=
    step.exists_original_protected_branch_operation he hF initial a b hab haint hpair hW haW
  have hK : K.faces.Finite := hR₀.subset hKR
  have old_chart (v : V3) (hvP₀ : v ∈ P₀.space) (hvJ : v ∈ interior J.space)
      (hvzero : (c v).2 = 0) :
      ∃ T : OpenPartialHomeomorph V3 C3,
        (0 : V3) ∈ T.source ∧ T 0 = 0 ∧ LocallyPiecewiseAffineOn T.symm T.target ∧
        (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔ (T z).1.1 = 0) ∧
        ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0 := by
    have hvP : v ∈ P.space := (hP₀s.subset hvP₀).1
    have hv0 : v ≠ 0 := by
      intro heq
      exact (hP₀s.subset hvP₀).2 (heq.symm ▸ mem_ball_self hρ)
    let y := Q.symm v
    have hyQ : y ∈ Q.source := Q.map_target (hJQ (interior_subset hvJ))
    have hQy : Q y = v := Q.right_inv (hJQ (interior_subset hvJ))
    obtain ⟨xr, ⟨⟨ur, hur, hru⟩, hxr⟩, hrv⟩ := (hPs.subset hvP).1
    have hyr : p xr = y := by
      have hxrQ : w.right xr ∈ Q.source := hxr.2
      rw [congrFun w.right_eq xr] at hxrQ
      apply Q.injOn hxrQ hyQ
      change Q (w.right xr) = v at hrv
      rw [congrFun w.right_eq xr] at hrv
      exact hrv.trans hQy.symm
    have hleft : y ∈ p '' (initial.map '' D ∩ w.left.source) :=
      (hplane y hyQ).mpr (by rw [hQy]; exact hvzero)
    obtain ⟨xl, ⟨⟨ul, hul, hlu⟩, hxl⟩, hly⟩ := hleft
    let al : D := ⟨ul, hul⟩
    let ar : D := ⟨ur, hur⟩
    have hlar : al ≠ ar := by
      intro heq
      have he : xl = xr :=
        hlu.symm.trans ((congrArg initial.map (congrArg Subtype.val heq)).trans hru)
      exact w.disjoint.ne_of_mem hxl hxr.1 he
    have hlower : lower al = y := (congrArg p hlu).trans hly
    have hupper : lower ar = y := (congrArg p hru).trans hyr
    have hnotE : ((al : V2), (ar : V2)) ∉ E := by
      intro hmem
      have hybad : y ∈ bad := ⟨((al : V2), (ar : V2)), hmem, hlower⟩
      have hyW := (hQW hyQ).1
      have hycenter : y = lower a := by
        by_contra hn
        exact hyW.2 ⟨hybad, hn⟩
      exact hv0 (hQy.symm.trans ((congrArg Q hycenter).trans hQzero))
    obtain ⟨a', b', w', c', T, horder, ha', hb', hyT, _hTinside, hTzero,
      hTPL, _hTbranches, _hTwhole, hTleft, hTright⟩ :=
      hcross al ar hlar (hlower.trans hupper.symm) hnotE Q.source Q.open_source
        (by change lower al ∈ Q.source; rw [hlower]; exact hyQ)
    have hyT' : y ∈ T.source := by
      change lower al ∈ T.source at hyT
      exact hlower ▸ hyT
    have hTy : T y = 0 := by
      change T (lower al) = 0 at hTzero
      simpa only [hlower] using hTzero
    obtain ⟨left, right, coord, hleftpoint, hrightpoint, hleq, hreq,
      hleftplane, hrightplane⟩ :
        ∃ (left right : OpenPartialHomeomorph t.Carrier s.Carrier)
          (coord : V3 ≃L[ℝ] C3),
          xl ∈ left.source ∧ xr ∈ right.source ∧
          (left : t.Carrier → s.Carrier) = p ∧
          (right : t.Carrier → s.Carrier) = p ∧
          (∀ x ∈ T.source, x ∈ p '' (initial.map '' D ∩ left.source) ↔
            (coord (T x)).2 = 0) ∧
          ∀ x ∈ T.source, x ∈ p '' (initial.map '' D ∩ right.source) ↔
            (coord (T x)).1.1 = 0 := by
      rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨w'.left, w'.right, c', hlu ▸ ha', hru ▸ hb',
          w'.left_eq, w'.right_eq, hTleft, hTright⟩
      · let perm : C3 ≃ₗ[ℝ] C3 :=
          { toFun := fun z => ((z.2, z.1.2), z.1.1)
            invFun := fun z => ((z.2, z.1.2), z.1.1)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        exact ⟨w'.right, w'.left, c'.trans perm.toContinuousLinearEquiv,
          hlu ▸ hb', hru ▸ ha', w'.right_eq, w'.left_eq, hTright, hTleft⟩
    let V := (w.left.target ∩ w.left.symm ⁻¹' left.source) ∩
      (w.right.target ∩ w.right.symm ⁻¹' right.source)
    have hV : IsOpen V := (w.left.symm.isOpen_inter_preimage left.open_source).inter
      (w.right.symm.isOpen_inter_preimage right.open_source)
    have hyV : y ∈ V := by
      have hly' : w.left xl = y := by rw [congrFun w.left_eq xl]; exact hly
      have hry' : w.right xr = y := by rw [congrFun w.right_eq xr]; exact hyr
      refine ⟨⟨hly' ▸ w.left.map_source hxl, ?_⟩,
        ⟨hry' ▸ w.right.map_source hxr.1, ?_⟩⟩
      · change w.left.symm y ∈ left.source
        rw [← hly', w.left.left_inv hxl]
        exact hleftpoint
      · change w.right.symm y ∈ right.source
        rw [← hry', w.right.left_inv hxr.1]
        exact hrightpoint
    have same_image (A B : OpenPartialHomeomorph t.Carrier s.Carrier)
        (hA : (A : t.Carrier → s.Carrier) = p)
        (hB : (B : t.Carrier → s.Carrier) = p) (x : s.Carrier)
        (hx : x ∈ A.target ∩ A.symm ⁻¹' B.source) :
        (x ∈ p '' (initial.map '' D ∩ A.source) ↔
          x ∈ p '' (initial.map '' D ∩ B.source)) := by
      have hp : p (A.symm x) = x := by rw [← hA]; exact A.right_inv hx.1
      have hAx := A.map_target hx.1
      constructor
      · rintro ⟨u, ⟨hu, huA⟩, hux⟩
        have heu : u = A.symm x := A.injOn huA hAx (by rw [hA]; exact hux.trans hp.symm)
        exact ⟨u, ⟨hu, heu.symm ▸ hx.2⟩, hux⟩
      · rintro ⟨u, ⟨hu, huB⟩, hux⟩
        have heu : u = A.symm x := B.injOn huB hx.2 (by rw [hB]; exact hux.trans hp.symm)
        exact ⟨u, ⟨hu, heu.symm ▸ hAx⟩, hux⟩
    obtain ⟨i, hyi⟩ := s.cover y
    let A := (s.charts i).symm.trans Q
    let B := (s.charts i).symm.trans T
    let F := A.symm.trans B
    have hF : F ∈ piecewiseAffineGroupoid V3 :=
      (piecewiseAffineGroupoid V3).trans ((piecewiseAffineGroupoid V3).symm (hQPL i)) (hTPL i)
    have hviA : v ∈ A.target := ⟨hJQ (interior_subset hvJ), hyi⟩
    have hviB : A.symm v ∈ B.source := by
      refine ⟨(s.charts i).map_source hyi, ?_⟩
      change (s.charts i).symm ((s.charts i) y) ∈ T.source
      rw [(s.charts i).left_inv hyi]
      exact hyT'
    have hvF : v ∈ F.source := ⟨hviA, hviB⟩
    have hFvalue (z : V3) (hz : z ∈ F.source) : F z = T (Q.symm z) := by
      change T ((s.charts i).symm ((s.charts i) (Q.symm z))) = T (Q.symm z)
      rw [(s.charts i).left_inv hz.1.2]
    let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
    have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
    have hshiftinv : shift.symm 0 = v := by rw [← hshift, shift.symm_apply_apply]
    let Dcoord := coord.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
    let H₀ := shift.symm.toHomeomorph.toOpenPartialHomeomorph.trans
      (F.trans Dcoord.toHomeomorph.toOpenPartialHomeomorph)
    let O := shift '' (interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' V))
    have hO : IsOpen O := shift.toHomeomorph.isOpenMap _
      (isOpen_interior.inter (Q.symm.isOpen_inter_preimage hV))
    let H := H₀.restrOpen O hO
    have hzeroH : (0 : V3) ∈ H.source := by
      refine ⟨⟨mem_univ _, ?_, mem_univ _⟩, ?_⟩
      · change shift.symm 0 ∈ F.source
        rw [hshiftinv]
        exact hvF
      · exact ⟨v, ⟨hvJ, hJQ (interior_subset hvJ), hyV⟩, hshift⟩
    have hHcenter : H 0 = 0 := by
      change Dcoord (F (shift.symm 0)) = 0
      rw [hshiftinv, hFvalue v hvF, hTy]
      exact map_zero coord
    have hHinv : LocallyPiecewiseAffineOn H.symm H.target := by
      have hfirst := hF.2.comp
        (locallyPiecewiseAffineOn_affine Dcoord.symm.toContinuousAffineMap isOpen_univ)
      have hsecond := (locallyPiecewiseAffineOn_affine
        shift.toContinuousAffineMap isOpen_univ).comp hfirst
      apply hsecond.mono H.open_target
      intro z hz
      exact ⟨⟨mem_univ _, hz.1.1.2⟩, mem_univ _⟩
    have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
    let Kshift := hshiftK.embeddedImage shift.injective.injOn
    have hKshifts : Kshift.space = shift '' K.space :=
      hshiftK.embeddedImage_space shift.injective.injOn
    let height : V3 →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
    have hheight (z : V3) : height (shift z) = (c z).2 := by
      change (c (-v + z)).2 = (c z).2
      rw [map_add, map_neg]
      change -(c v).2 + (c z).2 = (c z).2
      rw [hvzero, neg_zero, zero_add]
    have hparts (z : V3) (hz : z ∈ H.source) :
        (z ∈ Kshift.space ↔ (H z).1.1 = 0) ∧
          (height z = 0 ↔ (H z).2 = 0) := by
      let x := shift.symm z
      let y' := Q.symm x
      have hxF : x ∈ F.source := hz.1.2.1
      have hxJ : x ∈ interior J.space := by
        obtain ⟨a, ha, haz⟩ := hz.2
        change shift.symm z ∈ interior J.space
        rw [← haz, shift.symm_apply_apply]
        exact ha.1
      have hy'V : y' ∈ V := by
        obtain ⟨a, ha, haz⟩ := hz.2
        change Q.symm (shift.symm z) ∈ V
        rw [← haz, shift.symm_apply_apply]
        exact ha.2.2
      have hy'Q : y' ∈ Q.source := Q.map_target (hJQ (interior_subset hxJ))
      have hy'T : y' ∈ T.source := by
        have h := hxF.2.2
        change (s.charts i).symm ((s.charts i) y') ∈ T.source at h
        rwa [(s.charts i).left_inv hxF.1.2] at h
      have hQy' : Q y' = x := Q.right_inv (hJQ (interior_subset hxJ))
      have hrightimage : x ∈ K.space ↔
          y' ∈ p '' (initial.map '' D ∩ w.right.source) := by
        rw [hKs, hPs]
        constructor
        · rintro ⟨⟨u, ⟨hu, huT⟩, hux⟩, _⟩
          refine ⟨u, ⟨hu, huT.1⟩, ?_⟩
          have huQ : w.right u ∈ Q.source := huT.2
          rw [congrFun w.right_eq u] at huQ
          apply Q.injOn huQ hy'Q
          change Q (w.right u) = x at hux
          rw [congrFun w.right_eq u] at hux
          exact hux.trans hQy'.symm
        · rintro ⟨u, ⟨hu, huw⟩, huy⟩
          refine ⟨⟨u, ⟨hu, huw, ?_⟩, ?_⟩, interior_subset hxJ⟩
          · change w.right u ∈ Q.source
            rw [congrFun w.right_eq u]
            change p u ∈ Q.source
            rw [huy]
            exact hy'Q
          · change Q (w.right u) = x
            rw [congrFun w.right_eq u]
            change Q (p u) = x
            rw [huy, hQy']
      have hzeroimage : (c x).2 = 0 ↔
          y' ∈ p '' (initial.map '' D ∩ w.left.source) := by
        simpa only [hQy'] using (hplane y' hy'Q).symm
      have hback : z ∈ Kshift.space ↔ x ∈ K.space := by
        rw [hKshifts]
        constructor
        · rintro ⟨u, hu, huz⟩
          change shift.symm z ∈ K.space
          rwa [← huz, shift.symm_apply_apply]
        · intro h
          exact ⟨x, h, shift.apply_symm_apply z⟩
      have hheightback : height z = (c x).2 := by
        have hh := hheight x
        change height (shift (shift.symm z)) = (c x).2 at hh
        simpa only [shift.apply_symm_apply] using hh
      have hHval : H z = coord (T y') := by
        change Dcoord (F x) = coord (T y')
        rw [hFvalue x hxF]
        rfl
      constructor
      · rw [hback, hrightimage, same_image w.right right w.right_eq hreq y' hy'V.2,
          hrightplane y' hy'T, hHval]
      · rw [hheightback, hzeroimage, same_image w.left left w.left_eq hleq y' hy'V.1,
          hleftplane y' hy'T, hHval]
    refine ⟨H, hzeroH, hHcenter, hHinv, ?_, fun z hz => (hparts z hz).2⟩
    intro z hz
    change z ∈ shift '' K.space ↔ (H z).1.1 = 0
    rw [← hKshifts]
    exact (hparts z hz).1
  have happroach (v : V3) (hvP₀ : v ∈ P₀.space) (hvJ : v ∈ interior J.space)
      (hvzero : (c v).2 = 0) :
      v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
      v ∈ closure (K.space ∩ {z | (c z).2 < 0}) := by
    obtain ⟨H, hzeroH, hHcenter, _hHinv, hsheet, hflat⟩ := old_chart v hvP₀ hvJ hvzero
    let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
    have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
    have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
    let Kshift := hshiftK.embeddedImage shift.injective.injOn
    have hKshifts : Kshift.space = shift '' K.space :=
      hshiftK.embeddedImage_space shift.injective.injOn
    let height : V3 →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
    have hheight (z : V3) : height (shift z) = (c z).2 := by
      change (c (-v + z)).2 = (c z).2
      rw [map_add, map_neg]
      change -(c v).2 + (c z).2 = (c z).2
      rw [hvzero, neg_zero, zero_add]
    have hsigns := surface_signs Kshift height
      (c.symm ((0, 0), 1)) (by change (c (c.symm ((0, 0), 1))).2 = 1; rw [c.apply_symm_apply])
      H hzeroH hHcenter hflat (fun z hz => by rw [hKshifts]; exact hsheet z hz)
    have pull (test : ℝ → Prop)
        (hcl : (0 : V3) ∈ closure (Kshift.space ∩ {x | test (height x)})) :
        v ∈ closure (K.space ∩ {x | test ((c x).2)}) := by
      apply _root_.mem_closure_iff.mpr
      intro O hO hvO
      obtain ⟨z, hzO, hzK, hzt⟩ := _root_.mem_closure_iff.mp hcl (shift '' O)
        (shift.toHomeomorph.isOpenMap _ hO) ⟨v, hvO, hshift⟩
      obtain ⟨x, hxO, rfl⟩ := hzO
      have hxK : x ∈ K.space := shift.injective.mem_set_image.mp (hKshifts.subset hzK)
      have hxTest : test ((c x).2) := by
        rw [← hheight x]
        exact hzt
      exact ⟨x, hxO, hxK, hxTest⟩
    exact ⟨pull (fun x => 0 < x) hsigns.1, pull (fun x => x < 0) hsigns.2⟩
  have hcount (v : V3) (hv : v ∈ K₀.vertices) (hvJ : v ∈ interior J.space)
      (hvzero : (c v).2 = 0) :
      ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
      (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
      ∃ z ∈ (K.link v).space, (c z).2 < 0 := by
    have hvK : v ∈ K.vertices := hK₀K hv
    have hvP₀ : v ∈ P₀.space := hK₀s.subset (K₀.vertices_subset_space hv)
    obtain ⟨H, hzeroH, hHcenter, hHinv, hsheet, hflat⟩ := old_chart v hvP₀ hvJ hvzero
    let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
    have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
    have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
    let Kshift := hshiftK.embeddedImage shift.injective.injOn
    have hKshift : Kshift.faces.Finite := hshiftK.embeddedImage_finite shift.injective.injOn hK
    have hKshifts : Kshift.space = shift '' K.space :=
      hshiftK.embeddedImage_space shift.injective.injOn
    have hzeroKshift : (0 : V3) ∈ Kshift.vertices := by
      rw [hshiftK.embeddedImage_vertices shift.injective.injOn]
      exact ⟨v, hvK, hshift⟩
    let height : V3 →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
    have hheight (z : V3) : height (shift z) = (c z).2 := by
      change (c (-v + z)).2 = (c z).2
      rw [map_add, map_neg]
      change -(c v).2 + (c z).2 = (c z).2
      rw [hvzero, neg_zero, zero_add]
    have hparts (z : V3) (hz : z ∈ H.source) :
        (z ∈ Kshift.space ↔ (H z).1.1 = 0) ∧ (height z = 0 ↔ (H z).2 = 0) := by
      refine ⟨?_, hflat z hz⟩
      rw [hKshifts]
      exact hsheet z hz
    have hzeroCount := axis_count Kshift hKshift hzeroKshift height.toLinearMap
      H hzeroH hHcenter hHinv (fun z hz => and_congr (hparts z hz).1 (hparts z hz).2)
    have hsurface := surface_signs Kshift height
      (c.symm ((0, 0), 1)) (by change (c (c.symm ((0, 0), 1))).2 = 1; rw [c.apply_symm_apply])
      H hzeroH hHcenter (fun z hz => (hparts z hz).2) (fun z hz => (hparts z hz).1)
    have hsigns := Kshift.exists_both_link_signs_of_surface_accumulation
      hKshift hzeroKshift height.toLinearMap hsurface.1 hsurface.2
    have hlink : (Kshift.link 0).space = shift '' (K.link v).space := by
      have h := hshiftK.embeddedImage_link_space shift.injective.injOn hvK
      change (Kshift.link (shift v)).space = shift '' (K.link v).space at h
      simpa only [hshift] using h
    have hzeros : shift '' ((K.link v).space ∩ {z | (c z).2 = 0}) =
        (Kshift.link 0).space ∩ {z | height z = 0} := by
      rw [hlink]
      ext x
      constructor
      · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
        exact ⟨mem_image_of_mem shift hz, (hheight z).trans hz0⟩
      · rintro ⟨⟨z, hz, rfl⟩, hz0⟩
        exact ⟨z, ⟨hz, (hheight z).symm.trans hz0⟩, rfl⟩
    change ((Kshift.link 0).space ∩ {z | height z = 0}).ncard = 2 at hzeroCount
    rw [← hzeros, shift.injective.injOn.ncard_image] at hzeroCount
    obtain ⟨⟨u, hu, hupos⟩, v', hv', hvneg⟩ := hsigns
    obtain ⟨u', hu', rfl⟩ := hlink.subset hu
    obtain ⟨v'', hv'', rfl⟩ := hlink.subset hv'
    exact ⟨hzeroCount, ⟨u', hu', by
      calc
        0 < height (shift u') := hupos
        _ = (c u').2 := hheight u'⟩,
      v'', hv'', by
        calc
          (c v'').2 = height (shift v'') := (hheight v'').symm
          _ < 0 := hvneg⟩
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, fun x hx => ⟨(hQW hx).1.1, (hQW hx).2⟩,
    hQw, hQPL, hbranches, hplane, hJ, hJQ, hzeroJ, hρ, hball, hPs, hP₀s, hR₀, hR₀J,
    hKR, hKs, hqK, hqi.mono hKs.subset, hK₀K, hK₀s, hqint, hwhole,
    old_chart, happroach, hcount, hlinks,
    hL, hLs, hδ, hmargin, hmotions⟩

end Geometry.OriginalPLTower
