import deriv, json

functions = [
    "Real.exp x * (x^2 + 3)",
    "Real.cos (Real.log x)",
    "(Real.sin (2 * x - 1))^2",
    "x ^ 3 * (Real.log x / Real.log 5)",
    "(Real.log (5 * x + 2)) ^ 3",
    "Real.tan (5 * x)",
]

derivatives = [
    "(exp x0) * x0^2 + (exp x0) * 2 * x0 + 3 * exp x0",
    "-sin (log x0) / x0",
    "4 * sin (2 * x0 - 1) * cos (2 * x0 - 1)",
    "3 * x0 ^ 2 * Real.log x0 / Real.log 5 + x0 ^ 2 / Real.log 5",
    "15 * (Real.log (5 * x0 + 2)) ^ 2 / (5 * x0 + 2)",
    "5 / cos (5 * x0) ^ 2",
]

def expand(root):
    ...