import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Graphics3D

/-- A 3D point represented as three real coordinates -/
structure Point3D where
  x : ℝ
  y : ℝ
  z : ℝ

/-- A 3x3 rotation matrix -/
structure RotationMatrix where
  m00 : ℝ
  m01 : ℝ
  m02 : ℝ
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m20 : ℝ
  m21 : ℝ
  m22 : ℝ

/-- A translation vector -/
structure Translation where
  dx : ℝ
  dy : ℝ
  dz : ℝ

/-- Apply a rotation matrix to a 3D point -/
def rotate (R : RotationMatrix) (p : Point3D) : Point3D :=
  { x := R.m00 * p.x + R.m01 * p.y + R.m02 * p.z,
    y := R.m10 * p.x + R.m11 * p.y + R.m12 * p.z,
    z := R.m20 * p.x + R.m21 * p.y + R.m22 * p.z }

/-- Apply a translation to a 3D point -/
def translate (t : Translation) (p : Point3D) : Point3D :=
  { x := p.x + t.dx,
    y := p.y + t.dy,
    z := p.z + t.dz }

/-- Compute the squared norm (length squared) of a 3D point -/
def normSquared (p : Point3D) : ℝ :=
  p.x * p.x + p.y * p.y + p.z * p.z

/-- Compute the norm (length) of a 3D point -/
noncomputable def norm (p : Point3D) : ℝ :=
  Real.sqrt (normSquared p)

/-- A rotation matrix is orthogonal if its columns form an orthonormal basis.
    This is a key property that ensures rotations preserve distances. -/
def isOrthogonal (R : RotationMatrix) : Prop :=
  -- Column 1 · Column 1 = 1
  R.m00 * R.m00 + R.m10 * R.m10 + R.m20 * R.m20 = 1 ∧
  -- Column 2 · Column 2 = 1
  R.m01 * R.m01 + R.m11 * R.m11 + R.m21 * R.m21 = 1 ∧
  -- Column 3 · Column 3 = 1
  R.m02 * R.m02 + R.m12 * R.m12 + R.m22 * R.m22 = 1 ∧
  -- Column 1 · Column 2 = 0
  R.m00 * R.m01 + R.m10 * R.m11 + R.m20 * R.m21 = 0 ∧
  -- Column 1 · Column 3 = 0
  R.m00 * R.m02 + R.m10 * R.m12 + R.m20 * R.m22 = 0 ∧
  -- Column 2 · Column 3 = 0
  R.m01 * R.m02 + R.m11 * R.m12 + R.m21 * R.m22 = 0

/-- The identity rotation (no rotation) -/
def identityRotation : RotationMatrix :=
  { m00 := 1, m01 := 0, m02 := 0,
    m10 := 0, m11 := 1, m12 := 0,
    m20 := 0, m21 := 0, m22 := 1 }

/-- Rotation around the Z-axis by angle θ (in the XY plane) -/
noncomputable def rotationZ (θ : ℝ) : RotationMatrix :=
  { m00 := Real.cos θ, m01 := -Real.sin θ, m02 := 0,
    m10 := Real.sin θ, m11 :=  Real.cos θ, m12 := 0,
    m20 := 0,           m21 :=  0,          m22 := 1 }

/-- A transformation pipeline that first rotates, then translates -/
def transformPipeline (R : RotationMatrix) (t : Translation) (p : Point3D) : Point3D :=
  translate t (rotate R p)

/--
THEOREM: Orthogonal transformations preserve the squared norm.
This is a fundamental property in computer graphics: rotations don't change
the distance of a point from the origin.
-/

theorem rotation_preserves_norm_squared (R : RotationMatrix) (p : Point3D)
    (h : isOrthogonal R) :
    normSquared (rotate R p) = normSquared p := by
  unfold normSquared rotate isOrthogonal at *
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  -- The proof: expand the LHS and use orthogonality conditions
  calc (R.m00 * p.x + R.m01 * p.y + R.m02 * p.z) * (R.m00 * p.x + R.m01 * p.y + R.m02 * p.z) +
       (R.m10 * p.x + R.m11 * p.y + R.m12 * p.z) * (R.m10 * p.x + R.m11 * p.y + R.m12 * p.z) +
       (R.m20 * p.x + R.m21 * p.y + R.m22 * p.z) * (R.m20 * p.x + R.m21 * p.y + R.m22 * p.z)
    _ = p.x * p.x * (R.m00 * R.m00 + R.m10 * R.m10 + R.m20 * R.m20) +
        p.y * p.y * (R.m01 * R.m01 + R.m11 * R.m11 + R.m21 * R.m21) +
        p.z * p.z * (R.m02 * R.m02 + R.m12 * R.m12 + R.m22 * R.m22) +
        2 * p.x * p.y * (R.m00 * R.m01 + R.m10 * R.m11 + R.m20 * R.m21) +
        2 * p.x * p.z * (R.m00 * R.m02 + R.m10 * R.m12 + R.m20 * R.m22) +
        2 * p.y * p.z * (R.m01 * R.m02 + R.m11 * R.m12 + R.m21 * R.m22) := by ring
    _ = p.x * p.x * 1 + p.y * p.y * 1 + p.z * p.z * 1 +
        2 * p.x * p.y * 0 + 2 * p.x * p.z * 0 + 2 * p.y * p.z * 0 := by
          rw [h1, h2, h3, h4, h5, h6]
    _ = p.x * p.x + p.y * p.y + p.z * p.z := by ring

/--
THEOREM: Translation changes position but preserves relative distances.
The norm changes by a predictable amount based on the translation vector.
-/
theorem translation_norm_relation (t : Translation) (p : Point3D) :
    normSquared (translate t p) =
    normSquared p + 2 * (t.dx * p.x + t.dy * p.y + t.dz * p.z)
    + normSquared ⟨t.dx, t.dy, t.dz⟩ := by
  unfold normSquared translate
  ring

/--
THEOREM: The identity rotation leaves points unchanged.
-/
theorem identity_rotation_is_identity (p : Point3D) :
    rotate identityRotation p = p := by
  unfold rotate identityRotation
  simp

/--
THEOREM: The identity rotation is orthogonal.
-/
theorem identity_is_orthogonal : isOrthogonal identityRotation := by
  unfold isOrthogonal identityRotation
  simp

/--
THEOREM: Rotation around the Z-axis is orthogonal for any angle θ.
This uses the fundamental trigonometric identity: cos²θ + sin²θ = 1
-/
theorem rotationZ_is_orthogonal (θ : ℝ) : isOrthogonal (rotationZ θ) := by
  unfold isOrthogonal rotationZ
  constructor
  · simp; ring_nf; exact Real.cos_sq_add_sin_sq θ
  constructor
  · simp; ring_nf; rw [Real.sin_sq, Real.cos_sq]; ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

/-!
## Example Usage

Below we demonstrate the transformation pipeline with concrete values.
-/

/-- Example: A point at (1, 0, 0) -/
def examplePoint : Point3D := ⟨1, 0, 0⟩

/-- Example: Rotate 90 degrees around Z-axis -/
noncomputable def rotate90Z : RotationMatrix := rotationZ (Real.pi / 2)

/-- Example: Translate by (5, 3, 2) -/
def exampleTranslation : Translation := ⟨5, 3, 2⟩

/-- Apply the transformation pipeline -/
noncomputable def transformedPoint : Point3D :=
  transformPipeline rotate90Z exampleTranslation examplePoint

end Graphics3D

-- Check that definitions type-check
#check Graphics3D.Point3D
#check Graphics3D.rotate
#check Graphics3D.transformPipeline

-- Verify theorems are proven
#check Graphics3D.rotation_preserves_norm_squared
#check Graphics3D.identity_is_orthogonal
#check Graphics3D.rotationZ_is_orthogonal

-- Test with concrete values
open Graphics3D
#check transformedPoint
#eval examplePoint.x
