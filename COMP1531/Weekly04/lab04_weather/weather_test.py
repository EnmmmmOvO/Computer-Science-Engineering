"""
weather_test
"""
import weather

def test():
    """
    test 2008/12/02 Albury
    """
    assert(weather.weather("2008-12-02", "Albury") == (-0.98, 4.56))