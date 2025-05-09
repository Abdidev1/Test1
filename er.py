import math
import cmath
import statistics
import fractions
import decimal
from datetime import datetime, timedelta
import calendar
import random
import json
import csv
import os
import sys
import platform
import time
import logging
import re
import uuid
import hashlib
import base64
import urllib.parse
import inspect
import threading
import queue
import multiprocessing
import subprocess
import shlex
import zipfile
import tarfile
import gzip
import bz2
import lzma
import pickle
import copy
import enum
import collections
import heapq
import bisect
import array
import struct
import itertools
import functools
from typing import Union, Callable, Tuple, List, Dict, Any

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

class CalculatorError(Exception):
    """Custom exception class for calculator-related errors."""
    pass

class ScientificCalculator:
    """A comprehensive scientific calculator class with various functionalities."""

    def __init__(self):
        """Initializes the ScientificCalculator with memory and history."""
        self.memory = 0.0
        self.history: collections.deque[str] = collections.deque(maxlen=100)
        self._pi = math.pi
        self._e = math.e
        self._golden_ratio = (1 + math.sqrt(5)) / 2

    @property
    def pi(self) -> float:
        """Returns the value of pi."""
        return self._pi

    @property
    def e(self) -> float:
        """Returns the value of Euler's number (e)."""
        return self._e

    @property
    def golden_ratio(self) -> float:
        """Returns the value of the golden ratio."""
        return self._golden_ratio

    def _log_operation(self, expression: str, result: Union[float, complex, str]) -> None:
        """Logs the operation and its result to the history."""
        log_entry = f"{expression} = {result}"
        self.history.append(log_entry)
        logging.info(log_entry)

    def add(self, num1: float, num2: float) -> float:
        """Adds two numbers."""
        result = num1 + num2
        self._log_operation(f"{num1} + {num2}", result)
        return result

    def subtract(self, num1: float, num2: float) -> float:
        """Subtracts the second number from the first."""
        result = num1 - num2
        self._log_operation(f"{num1} - {num2}", result)
        return result

    def multiply(self, num1: float, num2: float) -> float:
        """Multiplies two numbers."""
        result = num1 * num2
        self._log_operation(f"{num1} * {num2}", result)
        return result

    def divide(self, num1: float, num2: float) -> float:
        """Divides the first number by the second."""
        if num2 == 0:
            raise CalculatorError("Division by zero is not allowed.")
        result = num1 / num2
        self._log_operation(f"{num1} / {num2}", result)
        return result

    def power(self, base: float, exponent: float) -> float:
        """Raises the base to the power of the exponent."""
        result = base ** exponent
        self._log_operation(f"{base} ^ {exponent}", result)
        return result

    def sqrt(self, num: float) -> float:
        """Calculates the square root of a non-negative number."""
        if num < 0:
            raise CalculatorError("Cannot calculate the square root of a negative real number. Use csqrt for complex numbers.")
        result = math.sqrt(num)
        self._log_operation(f"sqrt({num})", result)
        return result

    def csqrt(self, num: Union[float, complex]) -> complex:
        """Calculates the complex square root of a number."""
        result = cmath.sqrt(num)
        self._log_operation(f"csqrt({num})", result)
        return result

    def log(self, num: float, base: float = math.e) -> float:
        """Calculates the logarithm of a number with a given base (default is e)."""
        if num <= 0 or base <= 0 or base == 1:
            raise CalculatorError("Invalid input for logarithm.")
        result = math.log(num, base)
        self._log_operation(f"log({num}, {base})", result)
        return result

    def exp(self, num: float) -> float:
        """Calculates the exponential of a number (e raised to the power of num)."""
        result = math.exp(num)
        self._log_operation(f"exp({num})", result)
        return result

    def sin(self, angle: float) -> float:
        """Calculates the sine of an angle (in radians)."""
        result = math.sin(angle)
        self._log_operation(f"sin({angle})", result)
        return result

    def cos(self, angle: float) -> float:
        """Calculates the cosine of an angle (in radians)."""
        result = math.cos(angle)
        self._log_operation(f"cos({angle})", result)
        return result

    def tan(self, angle: float) -> float:
        """Calculates the tangent of an angle (in radians)."""
        if math.cos(angle) == 0:
            raise CalculatorError("Tangent is undefined for this angle.")
        result = math.tan(angle)
        self._log_operation(f"tan({angle})", result)
        return result

    def asin(self, num: float) -> float:
        """Calculates the arcsine (inverse sine) of a number (in radians)."""
        if not -1 <= num <= 1:
            raise CalculatorError("Input for arcsine must be between -1 and 1.")
        result = math.asin(num)
        self._log_operation(f"asin({num})", result)
        return result

    def acos(self, num: float) -> float:
        """Calculates the arccosine (inverse cosine) of a number (in radians)."""
        if not -1 <= num <= 1:
            raise CalculatorError("Input for arccosine must be between -1 and 1.")
        result = math.acos(num)
        self._log_operation(f"acos({num})", result)
        return result

    def atan(self, num: float) -> float:
        """Calculates the arctangent (inverse tangent) of a number (in radians)."""
        result = math.atan(num)
        self._log_operation(f"atan({num})", result)
        return result

    def factorial(self, num: int) -> int:
        """Calculates the factorial of a non-negative integer."""
        if not isinstance(num, int) or num < 0:
            raise CalculatorError("Input for factorial must be a non-negative integer.")
        result = math.factorial(num)
        self._log_operation(f"factorial({num})", result)
        return result

    def abs(self, num: float) -> float:
        """Calculates the absolute value of a number."""
        result = abs(num)
        self._log_operation(f"abs({num})", result)
        return result

    def floor(self, num: float) -> int:
        """Returns the floor of a number."""
        result = math.floor(num)
        self._log_operation(f"floor({num})", result)
        return result

    def ceil(self, num: float) -> int:
        """Returns the ceiling of a number."""
        result = math.ceil(num)
        self._log_operation(f"ceil({num})", result)
        return result

    def round(self, num: float, ndigits: int = None) -> float:
        """Rounds a number to a specified number of decimal places."""
        result = round(num, ndigits)
        self._log_operation(f"round({num}, {ndigits})", result)
        return result

    def memory_store(self, num: float) -> float:
        """Stores a number in the calculator's memory."""
        self.memory = num
        self._log_operation(f"Memory Store", num)
        return self.memory

    def memory_recall(self) -> float:
        """Recalls the number stored in the calculator's memory."""
        self._log_operation(f"Memory Recall", self.memory)
        return self.memory

    def memory_clear(self) -> float:
        """Clears the number stored in the calculator's memory."""
        self.memory = 0.0
        self._log_operation(f"Memory Clear", self.memory)
        return self.memory

    def memory_add(self, num: float) -> float:
        """Adds a number to the value in the calculator's memory."""
        self.memory += num
        self._log_operation(f"Memory Add {num}", self.memory)
        return self.memory

    def memory_subtract(self, num: float) -> float:
        """Subtracts a number from the value in the calculator's memory."""
        self.memory -= num
        self._log_operation(f"Memory Subtract {num}", self.memory)
        return self.memory

    def get_history(self) -> List[str]:
        """Returns the history of operations."""
        return list(self.history)

    def clear_history(self) -> None:
        """Clears the history of operations."""
        self.history.clear()
        logging.info("Calculator history cleared.")

    def mean(self, data: List[float]) -> float:
        """Calculates the mean of a list of numbers."""
        if not data:
            raise CalculatorError("Cannot calculate the mean of an empty list.")
        result = statistics.mean(data)
        self._log_operation(f"mean({data})", result)
        return result

    def median(self, data: List[float]) -> float:
        """Calculates the median of a list of numbers."""
        if not data:
            raise CalculatorError("Cannot calculate the median of an empty list.")
        result = statistics.median(data)
        self._log_operation(f"median({data})", result)
        return result

    def mode(self, data: List[Any]) -> List[Any]:
        """Calculates the mode(s) of a list of items."""
        if not data:
            raise CalculatorError("Cannot calculate the mode of an empty list.")
        try:
            result = statistics.mode(data)
            self._log_operation(f"mode({data})", result)
            return [result]
        except statistics.StatisticsError:
            result = statistics.multimode(data)
            self._log_operation(f"mode({data})", result)
            return result

    def standard_deviation(self, data: List[float]) -> float:
        """Calculates the standard deviation of a list of numbers."""
        if len(data) < 2:
            raise CalculatorError("Standard deviation requires at least two data points.")
        result = statistics.stdev(data)
        self._log_operation(f"stdev({data})", result)
        return result

    def variance(self, data: List[float]) -> float:
        """Calculates the variance of a list of numbers."""
        if len(data) < 2:
            raise CalculatorError("Variance requires at least two data points.")
        result = statistics.variance(data)
        self._log_operation(f"variance({data})", result)
        return result

    def gcd(self, a: int, b: int) -> int:
        """Calculates the greatest common divisor of two integers."""
        if not isinstance(a, int) or not isinstance(b, int):
            raise CalculatorError("Inputs for gcd must be integers.")
        result = math.gcd(a, b)
        self._log_operation(f"gcd({a}, {b})", result)
        return result

    def lcm(self, a: int, b: int) -> int:
        """Calculates the least common multiple of two integers."""
        if not isinstance(a, int) or not isinstance(b, int):
            raise CalculatorError("Inputs for lcm must be integers.")
        if a == 0 or b == 0:
            return 0
        result = abs(a * b) // math.gcd(a, b)
        self._log_operation(f"lcm({a}, {b})", result)
        return result

    def fraction(self, numerator: int, denominator: int) -> fractions.Fraction:
        """Creates a fraction object."""
        if not isinstance(numerator, int) or not isinstance(denominator, int):
            raise CalculatorError("Numerator and denominator must be integers.")
        if denominator == 0:
            raise CalculatorError("Denominator cannot be zero.")
        result = fractions.Fraction(numerator, denominator)
        self._log_operation(f"Fraction({numerator}, {denominator})", result)
        return result

    def decimal(self, value: Union[int, float, str, tuple]) -> decimal.Decimal:
        """Creates a decimal object with high precision."""
        try:
            result = decimal.Decimal(value)
            self._log_operation(f"Decimal({value})", result)
            return result
        except decimal.InvalidOperation:
            raise CalculatorError(f"Invalid input for decimal: {value}")

    def current_datetime(self) -> datetime:
        """Returns the current date and time."""
        now = datetime.now()
        self._log_operation("Current Datetime", now.isoformat())
        return now

    def time_difference(self, datetime1_str: str, datetime2_str: str, format_str: str = '%Y-%m-%d %H:%M:%S') -> timedelta:
        """Calculates the time difference between two datetime strings."""
        try:
            dt1 = datetime.strptime(datetime1_str, format_str)
            dt2 = datetime.strptime(datetime2_str, format_str)
            difference = abs(dt1 - dt2)
            self._log_operation(f"Time Difference ({datetime1_str}, {datetime2_str})", str(difference))
            return difference
        except ValueError:
            raise CalculatorError(f"Invalid datetime format. Please use: {format_str}")

    def day_of_week(self, date_str: str, format_str: str = '%Y-%m-%d') -> str:
        """Returns the day of the week for a given date string."""
        try:
            date_obj = datetime.strptime(date_str, format_str)
            day_name = calendar.day_name[date_obj.weekday()]
            self._log_operation(f"Day of Week ({date_str})", day_name)
            return day_name
        except ValueError:
            raise CalculatorError(f"Invalid date format. Please use: {format_str}")

    def generate_random_number(self, start: float, end: float) -> float:
        """Generates a random floating-point number within a specified range."""
        if start >= end:
            raise CalculatorError("Invalid range for random number generation.")
        result = random.uniform(start, end)
        self._log_operation(f"Random Number ({start}, {end})", result)
        return result

    def generate_random_integer(self, start: int, end: int) -> int:
        """Generates a random integer within a specified range (inclusive)."""
        if start > end:
            raise CalculatorError("Invalid range for random integer generation.")
        result = random.randint(start, end)
        self._log_operation(f"Random Integer ({start}, {end})", result)
        return result

    def shuffle_list(self, data: List[Any]) -> List[Any]:
        """Shuffles the elements of a list in place and returns the shuffled list."""
        temp_data = list(data)  # Create a copy to avoid modifying the original directly during logging
        random.shuffle(temp_data)
        self._log_operation(f"Shuffle List ({data})", temp_data)
        random.shuffle(data) # Shuffle the original list
        return data

    def choose_from_list(self, data: List[Any]) -> Any:
        """Chooses a random element from a list."""
        if not data:
            raise CalculatorError("Cannot choose from an empty list.")
        result = random.choice(data)
        self._log_operation(f"Choose from List ({data})", result)
        return result

    def sample_from_list(self, data: List[Any], k: int) -> List[Any]:
        """Returns a k length list of unique elements chosen from the population sequence."""
        if not data:
            raise CalculatorError("Cannot sample from an empty list.")
        if k > len(data):
            raise CalculatorError("Sample size cannot be larger than the population size.")
        result = random.sample(data, k)
        self._log_operation(f"Sample from List ({data}, {k})", result)
        return result