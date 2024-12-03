import requests, os, urllib.parse, json, re
from bs4 import BeautifulSoup

# appid = os.getenv('WA_APPID')
def make_wa_request(equation: str):
    appid = "hg3uu5-684ap4rhkp"
    query = urllib.parse.quote_plus(f"solve {equation}")
    query_url = f"http://api.wolframalpha.com/v2/query?" \
                f"appid={appid}" \
                f"&input={query}" \
                f"&scanner=Solve" \
                f"&podstate=Result__Step-by-step+solution" \
                "&format=plaintext" \
                f"&output=json"

    r = requests.get(query_url).json()

    data = r["queryresult"]["pods"][0]["subpods"]
    print(data)
    # result = data[0]["plaintext"]
    # steps = data[1]["plaintext"]

    # print(f"Result of {equation} is '{result}'.\n")
    # print(f"Possible steps to solution:\n\n{steps}")

urls = [
    ("https://tutorial.math.lamar.edu/Problems/CalcI/DiffFormulas.aspx", 0, 12),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/ProductQuotientRule.aspx", 0, 6),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/DiffTrigFcns.aspx", 3, 10),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/DiffExpLogFcns.aspx", 0, 6),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/DiffInvTrigFcns.aspx", 0, 5),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/DiffHyperFcns.aspx", 0, 3),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/ChainRule.aspx", 0, 27),
    ("https://tutorial.math.lamar.edu/Problems/CalcI/LogDiff.aspx", 0, 5),
]

# manually scraped: 
# https://byjus.com/maths/differentiation-questions/
# https://www.mathsgenie.co.uk/alevel/c1solomon/E1Qdif_B.pdf
# https://www.mathsgenie.co.uk/alevel/C3solomon/E3Qdif_E.pdf

manual = [
    "f(x) = \\bf{e}^{\\tan x}",
    "f(x) = (\\sin (2x+1))^2",
    "f(x) = \\log_7 (2x-3)",
    "f(x) = \\log_x 3",
    "f(x) = 3^{x\\log x}",
    "f(x) = \\frac{x+1}{x}",
    "f(x) = 3\\cot (x) + 5 \\csc (x)",
    "f(x) = \\frac{x + \cos (x)}{\\tan (x)}",
] + \
[
    "f(x) = x\\bf{e}^x",
    "f(x) = x(x+1)^4",
    "f(x)=x\\ln x",
    "f(x)=x^2(x-1)^3",
    "f(x)=x^3 \\ln (2x)",
    "f(x)=x^2\\bf{e}^{-x}",
    "f(x)=2x^4(5+x)^3",
    "f(x)=x^2(x-3)^4",
    "f(x)=x(2x-1)^3",
    "f(x)=x^2 \\ln (x+6)",
    "f(x)=x^4 \\bf{e}^3x",
    "f(x)=3x^4 \\bf{e}^{2x+3}",
    "f(x)=x(1-5x)^4",
    "f(x)=(x+1)\\ln (x^2 - 1)",
    "f(x)=x\\sqrt{x-1}",
    "f(x)=x^2 \\sqrt{3x + 1}",
    "f(x)=(x+2)(x-3)^3",
] + \
[
    "f(x) = x^5 + x^2",
    "f(x) = x + x^3",
    "f(x) = x^4 + 2",
    "f(x) = x^6 - 2x",
    "f(x) = 6x^3 + 5x^{-2}",
    "f(x) = x^2 - 4x + 1",
    "f(x) = x^{-1} - x^{-5}",
    "f(t) = t^6",
    "f(t) = 5t^{-3}",
    "f(t) = t^{1/2}",
    "f(t) = t^{2/3}",
    "f(t) = \\frac{3}{4}t^2",
    "f(t) = 8t^{\\frac{1}{4}}",
]

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
    
def write_to_txt(questions: list[str], filename: str = "webscraping/derivatives/HS/data.txt"):
    with open(filename, 'w') as file:
        for q in questions:
            file.write(q + '\n')

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

# question_bank = []
# for url, start, end in urls:
#     question_bank.extend(get_questions(url, start, end))

# question_bank = clean_bank(question_bank)

# question_bank.extend(manual)

# write_to_txt(question_bank)
            
# print(len(question_bank))

make_wa_request("7 + 2x = 12 - 3x")