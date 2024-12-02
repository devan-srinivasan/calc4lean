import requests, os, urllib.parse, json, re
from bs4 import BeautifulSoup

# appid = os.getenv('WA_APPID')

urls = [
    ("https://tutorial.math.lamar.edu/Problems/CalcII/IntegrationByParts.aspx", 0, 8),
    ("https://tutorial.math.lamar.edu/Problems/CalcII/IntegralsWithTrig.aspx", 0, 13),
    ("https://tutorial.math.lamar.edu/Problems/CalcII/PartialFractions.aspx", 0, 9),
    ("https://tutorial.math.lamar.edu/Problems/CalcII/IntegralsWithRoots.aspx", 0, 2),
    ("https://tutorial.math.lamar.edu/Problems/CalcII/IntegralsWithRoots.aspx", 0, 2),
    ("https://tutorial.math.lamar.edu/Problems/CalcII/IntegralsWithQuadratics.aspx", 0, 3),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/ComputingIndefiniteIntegrals.aspx",0,20),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/SubstitutionRuleIndefinite.aspx",0,15),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/SubstitutionRuleIndefinitePtII.aspx",0,12),
    
]

# manually scraped: 
# https://www.hollandcsd.org/cms/lib/NY19000531/Centricity/Domain/129/Basic%20Integration%20Problems.pdf

#manual = [
#    "$$\int (5x^2 - 8x + 5) \, dx ",
#    ""
#] + [
#] + [
#]

def get_questions(url, start, end):
    """
    Fetches the first n MathJax questions from the given URL.
    
    Args:
        url (str): The URL of the webpage containing the MathJax questions.
        n (int): The number of MathJax questions to fetch.
        
    Returns:
        list: A list of strings, each containing a MathJax question.
    """
    try:
        # Fetch the webpage content
        response = requests.get(url)
        response.raise_for_status()
        
        # Parse the HTML content
        soup = BeautifulSoup(response.text, 'html.parser')
        
        # Find all <script> elements with type="math/tex"
        practice_problems = soup.find('ol', class_='practice-problems')
        if practice_problems:
            questions = [li.get_text(strip=True)[:-8] for li in practice_problems.find_all('li')]
        else:
            print("ERROR: No <ol> of class 'practice-problems' found")
        
        return questions[start: end]
    
    except requests.exceptions.RequestException as e:
        print(f"An error occurred while fetching the URL: {e}")
        return []
    except Exception as e:
        print(f"An unexpected error occurred: {e}")
        return []
    
def write_to_txt(questions: list[str], filename: str = "webscraping/integrals/data.txt"):
    with open(filename, 'w') as file:
        for q in questions:
            file.write(q + '\n')

question_bank = []
for url, start, end in urls:
    question_bank.extend(get_questions(url, start, end))

def clean_bank(questions):
    def clean(q: str):
        to_remove = ['\\displaystyle', '\\left', '\\right', '\\,']
        for item in to_remove:
            q = q.replace(item, '')
        return q
    qb = []
    for q in questions:
        q_ = clean(q)
        q_ = q_[2:-2].strip()
        qb.append(q_)
    
    return qb


question_bank = clean_bank(question_bank)

#question_bank.extend(manual)

write_to_txt(question_bank)
            
print(len(question_bank))